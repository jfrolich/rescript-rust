//! Reading the header of a binary AST file.
//!
//! Port of `Binary_ast.read_header`, `header_dependencies` and
//! `header_source` (compiler/depends/binary_ast.ml). The header is a 4-byte
//! big-endian dependency-block length, the dependency block (module names,
//! each after a newline), the source path and a newline; the marshalled AST
//! follows (see `writer::write_ast_to_vec`).

const MAGIC_SEP_CHAR: u8 = b'\n';

/// Where the parts of an AST's header end: the dependency block takes the
/// bytes from 4 to `source_start`, the source path those up to `source_end`,
/// then a newline, and the marshalled AST follows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AstHeader {
    /// The offset of the source path, just after the dependency block.
    pub source_start: usize,
    /// The offset of the newline that ends the source path.
    pub source_end: usize,
}

/// `Binary_ast.read_header`: the header of an AST whose first bytes are
/// `contents`, or `None` when they end before the header does or give an
/// impossible length for the dependency block. The length is read as a
/// signed 32-bit integer, as `String.get_int32_be` does, and widened to `i64`
/// so that the bounds check cannot overflow on 32-bit targets.
pub fn read_header(contents: &[u8]) -> Option<AstHeader> {
    let length = contents.len();
    let prefix: [u8; 4] = contents.get(..4)?.try_into().ok()?;
    let source_start = 4 + i64::from(i32::from_be_bytes(prefix));
    if source_start < 4 || source_start > length as i64 {
        return None;
    }
    let source_start = source_start as usize;
    let newline = contents[source_start..]
        .iter()
        .position(|&byte| byte == MAGIC_SEP_CHAR)?;
    Some(AstHeader {
        source_start,
        source_end: source_start + newline,
    })
}

/// `Binary_ast.header_dependencies`: the module names in the dependency
/// block, without the empty name before its leading newline.
pub fn header_dependencies<'a>(contents: &'a [u8], header: &AstHeader) -> Vec<&'a [u8]> {
    contents[4..header.source_start]
        .split(|&byte| byte == MAGIC_SEP_CHAR)
        .filter(|name| !name.is_empty())
        .collect()
}

/// `Binary_ast.header_source`: the source path recorded in the header.
pub fn header_source<'a>(contents: &'a [u8], header: &AstHeader) -> &'a [u8] {
    &contents[header.source_start..header.source_end]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ast_with_header(block: &[u8], source: &[u8]) -> (Vec<u8>, usize) {
        let mut contents = (block.len() as u32).to_be_bytes().to_vec();
        contents.extend_from_slice(block);
        contents.extend_from_slice(source);
        contents.push(b'\n');
        let header_length = contents.len();
        // An opaque marshal prefix (magic and part of a header), not a whole
        // value: `read_header` never reads past the source path's newline.
        contents.extend_from_slice(&[0x84, 0x95, 0xA6, 0xBE, 0, 0, 0, 1, 0, 0, 0, 0]);
        (contents, header_length)
    }

    /// The header reads the same from every prefix of the file that holds it,
    /// as in tests/ounit_tests/ounit_compiler_request_tests.ml `ast_header`.
    #[test]
    fn header_reads_the_same_from_every_prefix_that_holds_it() {
        let (contents, header_length) = ast_with_header(b"\nBelt\nJs\n", b"/src/A.res");
        let header = read_header(&contents).expect("a whole AST has a header");
        let dependencies: Vec<&[u8]> = vec![b"Belt", b"Js"];
        assert_eq!(header_dependencies(&contents, &header), dependencies);
        assert_eq!(header_source(&contents, &header), b"/src/A.res");
        for length in 0..=contents.len() {
            let expected = (length >= header_length).then_some(header);
            assert_eq!(
                read_header(&contents[..length]),
                expected,
                "the first {length} bytes"
            );
        }
    }

    #[test]
    fn damaged_headers_have_no_header() {
        for (name, damaged) in [
            ("Short", b"\x00\x00".to_vec()),
            ("Negative", b"\xff\xff\xff\xff\nA\n/a.res\n".to_vec()),
            ("MostNegative", b"\x80\x00\x00\x00\nA\n/a.res\n".to_vec()),
            ("Huge", b"\x3f\xff\xff\xffshort".to_vec()),
            ("Largest", b"\x7f\xff\xff\xffshort".to_vec()),
            ("PastEnd", b"\x00\x00\x00\x09\nA\n".to_vec()),
            ("Unterminated", b"\x00\x00\x00\x01\n/src/A.res".to_vec()),
            ("BlockOnly", b"\x00\x00\x00\x01\n".to_vec()),
        ] {
            assert_eq!(read_header(&damaged), None, "{name}");
        }
    }

    #[test]
    fn newline_at_the_last_byte_ends_the_header() {
        let contents = b"\x00\x00\x00\x01\n/src/A.res\n";
        assert_eq!(
            read_header(contents),
            Some(AstHeader {
                source_start: 5,
                source_end: contents.len() - 1,
            })
        );
    }

    /// `read_header` accepts an empty source path, as OCaml's does; callers
    /// that need a path reject it themselves.
    #[test]
    fn empty_source_path_is_a_header() {
        let contents = b"\x00\x00\x00\x01\n\n";
        let header = read_header(contents).expect("an empty source is a header");
        assert_eq!(header_source(contents, &header), b"");
        assert!(header_dependencies(contents, &header).is_empty());
        // A zero-length dependency block is not one the writer makes, but
        // reads like OCaml's: the source starts right after the length.
        let contents = b"\x00\x00\x00\x00/a.res\n";
        let header = read_header(contents).expect("a header");
        assert_eq!(header_source(contents, &header), b"/a.res");
        assert!(header_dependencies(contents, &header).is_empty());
    }
}
