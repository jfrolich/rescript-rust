#!/usr/bin/env python3
import importlib.util,os,tempfile,unittest
from pathlib import Path
S=Path(__file__).with_name('rollback_comparison_measure.py');os.chdir(S.parents[1]);spec=importlib.util.spec_from_file_location('r',S);r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
class Tests(unittest.TestCase):
 def test_order(self):
  self.assertEqual(len(r.rows()),32);self.assertEqual(r.rows()[:4],[[1,1,1,'M',12],[1,1,2,'R',12],[1,2,1,'M',1],[1,2,2,'R',1]]);self.assertEqual(r.rows()[4:8],[[2,1,1,'R',1],[2,1,2,'M',1],[2,2,1,'R',12],[2,2,2,'M',12]])
  with self.assertRaises(RuntimeError):r.slot(1,1,'M',1)
 def test_metrics(self):
  with self.assertRaises(RuntimeError):r.metrics('real 1\nuser 1\nsys 1\n')
 def test_inner(self):
  with tempfile.TemporaryDirectory() as d:
   p=Path(d)/'x';x=r.inner(['/bin/sh','-c','echo durable; echo err >&2'],os.environ.copy(),p);self.assertEqual(x['exit'],0);self.assertEqual(Path(str(p)+'.stdout').read_text().strip(),'durable')
   with self.assertRaises(RuntimeError):r.inner(['/usr/bin/true'],os.environ.copy(),p)
 def test_metadata(self):self.assertEqual(len(r.metadata()),12)
if __name__=='__main__':unittest.main()
