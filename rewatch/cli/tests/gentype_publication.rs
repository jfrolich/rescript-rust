//! Exercise the publication guards in the debug-profile CI test job.
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

#[test]
fn gentype_declarations_are_available_to_dependents() {
    let project = tempfile::tempdir().unwrap();
    let root = project.path();
    std::fs::create_dir(root.join("src")).unwrap();
    std::fs::write(
        root.join("rescript.json"),
        r#"{"name":"gentype-publication","sources":["src"],"gentypeconfig":{},"package-specs":{"module":"esmodule","in-source":true},"suffix":".res.js"}"#,
    ).unwrap();
    std::fs::write(root.join("src/Provider.res"), "@genType\ntype t = {value: int}\n").unwrap();
    std::fs::write(
        root.join("src/Consumer.res"),
        "@genType\nlet read = (x: Provider.t) => x.value\n",
    )
    .unwrap();

    let log = std::fs::File::create(root.join("build.log")).unwrap();
    let mut child = Command::new(env!("CARGO_BIN_EXE_rescript"))
        .arg("build")
        .current_dir(root)
        .env(
            "RESCRIPT_RUNTIME",
            concat!(env!("CARGO_MANIFEST_DIR"), "/../../packages/@rescript/runtime"),
        )
        .env("RUST_BACKTRACE", "1")
        .env("RAYON_NUM_THREADS", "2")
        .stdout(Stdio::from(log.try_clone().unwrap()))
        .stderr(Stdio::from(log))
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(10);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!(
                "genType build timed out: {}",
                std::fs::read_to_string(root.join("build.log")).unwrap()
            );
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    assert!(
        status.success(),
        "{}",
        std::fs::read_to_string(root.join("build.log")).unwrap()
    );
    let provider = std::fs::read_to_string(root.join("src/Provider.gen.tsx")).unwrap();
    let consumer = std::fs::read_to_string(root.join("src/Consumer.gen.tsx")).unwrap();
    assert!(provider.contains("export type t"), "{provider}");
    assert!(consumer.contains("Provider.gen"), "{consumer}");
    assert!(consumer.contains("export const read"), "{consumer}");
}
