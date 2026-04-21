
#[test]
fn comptime_inline_direct_call() {
    let source = r#"
@comptime.inline
let upperCase = (value) => String.toUpperCase(value)

let upperStr = upperCase("Bla")
"#;
    let result = compile_with_stdlib(source, "comptime_inline_direct.res");
    match result {
        Ok(output) => {
            eprintln!("=== INLINE DIRECT ===\n{}\n=== END ===", output);
        }
        Err(e) => panic!("compile failed: {e}"),
    }
}

#[test]
fn comptime_type_decl_call() {
    let source = std::fs::read_to_string("/tmp/test_typedecl.res").unwrap();
    match compile_with_stdlib(&source, "typedecl.res") {
        Ok(o) => eprintln!("OK:\n{o}"),
        Err(e) => eprintln!("FAIL: {e}"),
    }
}
