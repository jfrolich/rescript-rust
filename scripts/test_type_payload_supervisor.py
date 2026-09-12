import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock

import type_payload_supervisor as supervisor


class CaptureTests(unittest.TestCase):
    def setUp(self):
        # Retain synthetic fixtures and process evidence, including failed tests.
        self.root = Path(tempfile.mkdtemp(prefix="type-payload-supervisor-"))
        self.prefix = self.root / "command"

    def run_code(self, code, **options):
        return supervisor.capture(
            [sys.executable, "-c", code], self.prefix,
            env=os.environ.copy(), timeout=options.pop("timeout", 3),
            term_grace=options.pop("term_grace", 0.3), kill_grace=3,
            **options)

    def assert_reaped(self, result):
        self.assertTrue(result["leader_reaped"], result)
        self.assertTrue(result["group_absent"], result)
        self.assertFalse(result["cleanup_errors"], result)
        self.assertFalse(supervisor.group_exists(result["pgid"]))

    def test_success_and_publication(self):
        result = self.run_code("print('captured')")
        supervisor.require_success(result)
        self.assert_reaped(result)
        self.assertEqual(Path(str(self.prefix) + ".stdout").read_text(), "captured\n")
        self.assertEqual(json.loads(Path(str(self.prefix) + ".process.json").read_text()), result)
        self.assertGreater(result["wall_ns"], 0)

    def test_nested_success_requires_matching_reaping_evidence(self):
        nested_prefix = self.root / "nested"
        code = f"""
import os,sys
sys.path.insert(0,{str(Path(supervisor.__file__).parent)!r})
import type_payload_supervisor as s
result=s.capture([sys.executable,'-c',"print('nested')"],{str(nested_prefix)!r},
                 env=os.environ.copy(),timeout=3,token='test')
s.require_success(result)
"""
        result = self.run_code(code, token="test", children=[
            (str(nested_prefix) + ".pid.json", str(nested_prefix) + ".process.json")])
        supervisor.require_success(result)
        self.assert_reaped(result)
        self.assertEqual(list(result["nested_reaping"].values()), [True])

    def test_missing_nested_evidence_invalidates_success(self):
        result = self.run_code("print('no child')", children=[
            (self.root / "missing.pid", self.root / "missing.complete")])
        self.assertIn("evidence incomplete", result["error"])
        self.assert_reaped(result)

    def test_nonzero_is_not_success(self):
        result = self.run_code("raise SystemExit(7)")
        self.assertEqual(result["exit"], 7)
        self.assert_reaped(result)
        with self.assertRaises(RuntimeError):
            supervisor.require_success(result)

    def test_permission_error_is_not_group_absence(self):
        with mock.patch.object(supervisor.os, "killpg", side_effect=PermissionError):
            self.assertTrue(supervisor.group_exists(123456))

    def test_partial_replay_is_zero_launch(self):
        Path(str(self.prefix) + ".started.json.publishing-partial").write_text("{}")
        with mock.patch.object(supervisor.subprocess, "Popen") as launch:
            with self.assertRaises(RuntimeError):
                self.run_code("raise SystemExit('must not launch')")
            launch.assert_not_called()

    def test_timeout_escalates_and_reaps(self):
        result = self.run_code(
            "import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(30)",
            timeout=0.3)
        self.assertTrue(result["timeout"])
        self.assert_reaped(result)
        self.assertIn("SIGKILL", [row["signal"] for row in result["cleanup"]])

    def test_leader_success_does_not_hide_stubborn_descendant(self):
        ready = self.root / "ready"
        code = f"""
import os,signal,time
from pathlib import Path
child=os.fork()
if child==0:
    signal.signal(signal.SIGTERM,signal.SIG_IGN)
    os.close(1);os.close(2)
    Path({str(ready)!r}).write_text('ready')
    time.sleep(30)
else:
    while not Path({str(ready)!r}).exists():time.sleep(.005)
"""
        result = self.run_code(code)
        self.assertEqual(result["exit"], 0)
        self.assertIn("surviving descendants", result["error"])
        self.assert_reaped(result)
        self.assertIn("SIGKILL", [row["signal"] for row in result["cleanup"]])

    def test_nested_group_survives_leader_but_not_cleanup(self):
        pid, complete, ready = [self.root / name for name in ("nested.pid", "nested.complete", "ready")]
        nested = ("import signal,time;from pathlib import Path;"
                  "signal.signal(signal.SIGTERM,signal.SIG_IGN);"
                  f"Path({str(ready)!r}).write_text('ready');time.sleep(30)")
        code = f"""
import os,sys,json,subprocess,time
from pathlib import Path
p=subprocess.Popen([sys.executable,'-c',{nested!r}],start_new_session=True,
                   stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
while not Path({str(ready)!r}).exists():time.sleep(.005)
Path({str(pid)!r}).write_text(json.dumps({{'pgid':p.pid,'owner_group':os.getpgrp(),'token':'test'}}))
"""
        result = self.run_code(code, token="test", children=[(pid, complete)])
        self.assertIn("surviving descendants", result["error"])
        self.assert_reaped(result)
        self.assertFalse(supervisor.group_exists(json.loads(pid.read_text())["pgid"]))

    def test_untrusted_record_never_signals_foreign_group(self):
        other = subprocess.Popen([sys.executable, "-c", "import time;time.sleep(30)"],
                                 start_new_session=True)
        pid, complete = self.root / "foreign.pid", self.root / "foreign.complete"
        try:
            code = f"""
import json,os
from pathlib import Path
Path({str(pid)!r}).write_text(json.dumps({{'pgid':{other.pid},'owner_group':os.getpgrp(),'token':'wrong'}}))
"""
            result = self.run_code(code, token="test", children=[(pid, complete)])
            self.assertTrue(result["error"])
            self.assertTrue(result["cleanup_errors"])
            self.assertIsNone(other.poll())
            self.assertNotIn(other.pid, [x["pgid"] for x in result["cleanup"]])
        finally:
            os.killpg(other.pid, signal.SIGKILL)
            other.wait(timeout=3)

    def test_publication_failure_after_spawn_still_reaps(self):
        publish = supervisor.publish

        def fail_pid(path, value):
            if str(path).endswith(".pid.json"):
                raise OSError("synthetic publication failure")
            return publish(path, value)

        with mock.patch.object(supervisor, "publish", side_effect=fail_pid):
            result = self.run_code("import time;time.sleep(30)")
        self.assertIn("synthetic publication failure", result["error"])
        self.assert_reaped(result)

    def test_interrupt_is_not_swallowed_by_communicate(self):
        errors = []

        def trigger():
            deadline = time.monotonic() + 3
            while not Path(str(self.prefix) + ".pid.json").exists():
                if time.monotonic() > deadline:
                    errors.append("no process appeared")
                    return
                time.sleep(.005)
            os.kill(os.getpid(), signal.SIGTERM)

        with supervisor.handle_interrupts():
            thread = threading.Thread(target=trigger)
            thread.start()
            result = self.run_code("import time;time.sleep(30)")
            thread.join(timeout=4)
        self.assertFalse(errors)
        self.assertFalse(thread.is_alive())
        self.assertIn("SupervisorInterrupted", result["error"])
        self.assert_reaped(result)

    def test_allows_inner_reaping_after_outer_leader_exits(self):
        pid, complete = self.root / "nested.pid", self.root / "nested.complete"
        code = f"""
import os,sys,signal,time,json,subprocess
from pathlib import Path
if os.fork()==0:
    os.close(1);os.close(2)
    p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(30)'],start_new_session=True,
                       stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
    def finish(sig,frame):
        os.killpg(p.pid,signal.SIGTERM);p.wait()
        time.sleep(.2)
        Path({str(complete)!r}).write_text(json.dumps({{'token':'test','pgid':p.pid,'leader_reaped':True,'group_absent':True}}))
        os._exit(0)
    signal.signal(signal.SIGTERM,finish)
    Path({str(pid)!r}).write_text(json.dumps({{'token':'test','pgid':p.pid,'owner_group':os.getpgrp()}}))
    while True:time.sleep(1)
else:
    while not Path({str(pid)!r}).exists():time.sleep(.005)
    raise SystemExit(7)
"""
        result = self.run_code(code, token="test", children=[(pid, complete)], term_grace=1)
        self.assert_reaped(result)
        self.assertTrue(result["nested_reaping"][str(pid)])
        self.assertNotIn("SIGKILL", [x["signal"] for x in result["cleanup"]])


if __name__ == "__main__":
    unittest.main()
