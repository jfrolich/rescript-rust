//! URIs: analysis/src/uri.ml over the `lsp` library's `Uri` (uri0.ml and
//! uri_lexer.mll of lsp 1.25.0, the subset analysis uses).
//!
//! The analysis keeps a file's URI as its path; these turn paths into the
//! strings LSP responses carry.

/// `Lsp.Uri.t`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LspUri {
    pub scheme: String,
    pub authority: String,
    pub path: String,
}

/// `Lsp.Uri.of_path` (`Uri_lexer.of_path`, POSIX).
pub fn of_path(path: &str) -> LspUri {
    let file = |authority: &str, path: String| LspUri {
        scheme: "file".to_string(),
        authority: authority.to_string(),
        path,
    };
    if path.is_empty() {
        file("", "/".to_string())
    } else if let Some(rest) = path.strip_prefix("//") {
        match rest.find('/') {
            Some(slash) => file(&rest[..slash], rest[slash..].to_string()),
            None => file(rest, "/".to_string()),
        }
    } else if path.starts_with('/') {
        file("", path.to_string())
    } else {
        file("", format!("/{path}"))
    }
}

fn hex_value(c: u8) -> Option<u8> {
    (c as char).to_digit(16).map(|d| d as u8)
}

/// `Uri_lexer.decode`.
fn decode(s: &str) -> String {
    let b = s.as_bytes();
    let mut out = Vec::with_capacity(b.len());
    let mut i = 0;
    while i < b.len() {
        if b[i] != b'%' {
            out.push(b[i]);
            i += 1;
            continue;
        }
        i += 1;
        match b.get(i).and_then(|c| hex_value(*c)) {
            None if i >= b.len() => out.push(b'%'),
            None => out.push(b'%'),
            Some(high) => {
                i += 1;
                match b.get(i) {
                    None => {
                        out.push(b'%');
                        out.push(b[i - 1]);
                    }
                    Some(c) => match hex_value(*c) {
                        Some(low) => {
                            out.push((high << 4) + low);
                            i += 1;
                        }
                        None => {
                            out.push(b'%');
                            out.push(b[i - 1]);
                        }
                    },
                }
            }
        }
    }
    String::from_utf8_lossy(&out).into_owned()
}

/// `Lsp.Uri.of_string` (`Uri_lexer.uri`), without query and fragment, which
/// analysis URIs never carry.
pub fn of_string(s: &str) -> LspUri {
    let (scheme, rest) = match s.find([':', '/', '?', '#']) {
        Some(i) if i > 0 && s.as_bytes()[i] == b':' => (s[..i].to_string(), &s[i + 1..]),
        _ => ("file".to_string(), s),
    };
    let (authority, rest) = match rest.strip_prefix("//") {
        Some(after) => {
            let end = after.find(['/', '?', '#']).unwrap_or(after.len());
            (decode(&after[..end]), &after[end..])
        }
        None => (String::new(), rest),
    };
    let end = rest.find(['?', '#']).unwrap_or(rest.len());
    let mut path = decode(&rest[..end]);
    if matches!(scheme.as_str(), "http" | "https" | "file") && !path.starts_with('/') {
        path.insert(0, '/');
    }
    LspUri {
        scheme,
        authority,
        path,
    }
}

/// `Uri0.encode`.
fn encode(s: &str, allow_slash: bool) -> String {
    let mut out = String::with_capacity(s.len());
    for &c in s.as_bytes() {
        if (allow_slash && c == b'/')
            || c.is_ascii_alphanumeric()
            || matches!(c, b'_' | b'.' | b'-' | b'~')
        {
            out.push(c as char);
        } else {
            out.push_str(&format!("%{c:02X}"));
        }
    }
    out
}

/// `Lsp.Uri.to_string`.
pub fn to_lsp_string(uri: &LspUri) -> String {
    let mut buff = String::new();
    if !uri.scheme.is_empty() {
        buff.push_str(&uri.scheme);
        buff.push(':');
    }
    if !uri.authority.is_empty() || uri.scheme == "file" {
        buff.push_str("//");
    }
    if !uri.authority.is_empty() {
        buff.push_str(&encode(&uri.authority.to_ascii_lowercase(), false));
    }
    let path = uri.path.as_bytes();
    let len = path.len();
    if len > 0 {
        if len >= 3 && path[0] == b'/' && path[2] == b':' {
            let drive = path[1].to_ascii_lowercase();
            if drive.is_ascii_lowercase() {
                buff.push('/');
                buff.push(drive as char);
                buff.push_str("%3A");
                buff.push_str(&encode(&uri.path[3..], true));
            }
        } else if len >= 2 && path[1] == b':' {
            let drive = path[0].to_ascii_lowercase();
            if drive.is_ascii_lowercase() {
                buff.push(drive as char);
                buff.push_str("%3A");
                buff.push_str(&encode(&uri.path[2..], true));
            }
        } else {
            buff.push_str(&encode(&uri.path, true));
        }
    }
    buff
}

/// `Lsp.Uri.to_path` (POSIX, no query).
pub fn lsp_to_path(uri: &LspUri) -> String {
    let path = &uri.path;
    if path.is_empty() {
        return "/".to_string();
    }
    if !uri.authority.is_empty() && path.len() > 1 && uri.scheme == "file" {
        return format!("//{}{}", uri.authority, path);
    }
    let b = path.as_bytes();
    if b.len() >= 3 && b[0] == b'/' && b[1].is_ascii_alphabetic() && b[2] == b':' {
        format!("{}{}", (b[1] as char).to_ascii_lowercase(), &path[2..])
    } else {
        path.clone()
    }
}

/// How the analysis prints URIs: `Uri.strip_path` is set by the test
/// command, so expectations do not depend on where the tests are checked
/// out.
#[derive(Debug, Clone, Copy, Default)]
pub struct UriStyle {
    pub strip_path: bool,
}

impl UriStyle {
    /// `Uri.to_string` of `Uri.from_path path`.
    pub fn to_string(self, path: &str) -> String {
        if self.strip_path {
            let p = lsp_to_path(&of_path(path));
            p.rsplit('/').next().unwrap_or(&p).to_string()
        } else {
            to_lsp_string(&of_path(path))
        }
    }

    /// `Uri.to_path` of `Uri.from_path path`: the test style drops the
    /// leading `/`.
    pub fn to_path(self, path: &str) -> String {
        let p = lsp_to_path(&of_path(path));
        if self.strip_path {
            p[1..].to_string()
        } else {
            p
        }
    }

    /// `Uri.to_string uri |> Uri.from_path`, as LSP prints it.
    pub fn lsp_string_of_path_string(self, path: &str) -> String {
        to_lsp_string(&of_path(&self.to_string(path)))
    }

    /// `Files.canonicalize_uri |> Uri.from_string`, as LSP prints it.
    pub fn canonical_lsp_string(self, path: &str) -> String {
        let path = std::fs::canonicalize(path)
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_else(|_| path.to_string());
        to_lsp_string(&of_string(&self.to_string(&path)))
    }

    /// `Uri.to_string uri |> Uri.from_string`, as LSP prints it.
    pub fn lsp_string(self, path: &str) -> String {
        to_lsp_string(&of_string(&self.to_string(path)))
    }
}

/// `Uri.is_interface`. OCaml writes `uri |> Lsp.Uri.to_string |>
/// Filename.check_suffix "i"`, which asks whether `"i"` ends with the URI:
/// false for every file. Interface handling across the analysis (and its
/// expected test output) follows from that, so it is kept. `of_path`
/// always gives a `file:` URI, so the answer is computed without building it.
pub fn is_interface(_path: &str) -> bool {
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prints_test_and_editor_uris() {
        let test = UriStyle { strip_path: true };
        assert_eq!(
            test.lsp_string("/a/b/Definition.res"),
            "file:///Definition.res"
        );
        let editor = UriStyle::default();
        assert_eq!(editor.lsp_string("/a b/C.res"), "file:///a%20b/C.res");
        assert!(!is_interface("/a/C.resi"));
    }
}
