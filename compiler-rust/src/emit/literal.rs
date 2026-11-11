//! JS string values decode valid UTF-8 runs and map invalid bytes to Latin-1.
pub(super) fn string_value(s: &str) -> String {
    let bytes = crate::string_literal::bytes_of(s);
    let mut result = String::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        let (valid, _, len) = crate::string_literal::get_utf_8_uchar(&bytes, i);
        if valid {
            result.push_str(std::str::from_utf8(&bytes[i..i + len]).expect("valid UTF-8"));
            i += len;
        } else {
            result.push(char::from(bytes[i]));
            i += 1;
        }
    }
    result
}
