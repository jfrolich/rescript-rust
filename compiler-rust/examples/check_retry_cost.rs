//! Full-compilation cost probe: SOURCE followed by `pass` or `fail`.
//! Includes parsing/checking and, on success, the backend; no CLI preparation.
fn main() {
    let path = std::env::args().nth(1).expect("source path");
    let should_fail = std::env::args().nth(2).as_deref() == Some("fail");
    std::thread::Builder::new().stack_size(64 * 1024 * 1024).spawn(move || {
        let source = std::fs::read_to_string(path).unwrap();
        let options = rescript_compiler::driver::CompilerOptions {
            nopervasives: true,
            ..Default::default()
        };
        let result = rescript_compiler::driver::compile_source_to_js_with_options(&source, "Unit.res", &options);
        assert_eq!(result.is_err(), should_fail, "{result:?}");
        std::hint::black_box(result).ok();
    }).unwrap().join().unwrap();
}
