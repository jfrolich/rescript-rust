//! Compare mapped segments in generated token order, ignoring generated line and
//! column. Resolve source/name indices to strings and remove consecutive equal
//! (source, original UTF-16 line/column, name) tuples. Unmapped segments do not
//! enter the sequence. The emitter removes synthetic end tokens before writing
//! JSON; this helper does NOT guess which original mappings are end tokens.
use serde_json::Value;

pub fn sequence(json: &str) -> Vec<(String, i64, i64, Option<String>)> {
    let map: Value = serde_json::from_str(json).unwrap();
    let mut source = 0i64;
    let mut line = 0i64;
    let mut column = 0i64;
    let mut name = 0i64;
    let mut result = Vec::new();
    for segment in map["mappings"]
        .as_str()
        .unwrap()
        .split([';', ','])
        .filter(|s| !s.is_empty())
    {
        let mut fields = Vec::new();
        let mut value = 0i64;
        let mut shift = 0;
        for byte in segment.bytes() {
            let digit = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
                .iter()
                .position(|b| *b == byte)
                .expect("VLQ alphabet") as i64;
            value |= (digit & 31) << shift;
            if digit & 32 == 0 {
                fields.push(if value & 1 == 1 {
                    -(value >> 1)
                } else {
                    value >> 1
                });
                value = 0;
                shift = 0;
            } else {
                shift += 5;
            }
        }
        assert_eq!(shift, 0, "unterminated VLQ");
        if fields.len() == 1 {
            continue;
        }
        assert!(fields.len() == 4 || fields.len() == 5);
        source += fields[1];
        line += fields[2];
        column += fields[3];
        let mapped_name = if fields.len() == 5 {
            name += fields[4];
            Some(map["names"][name as usize].as_str().unwrap().to_owned())
        } else {
            None
        };
        let tuple = (
            map["sources"][source as usize].as_str().unwrap().to_owned(),
            line,
            column,
            mapped_name,
        );
        if result.last() != Some(&tuple) {
            result.push(tuple);
        }
    }
    result
}

#[test]
fn ignores_layout_but_not_order_names_or_positions() {
    let map = |m: &str| format!(r#"{{"sources":["a.res"],"names":["x"],"mappings":"{m}"}}"#);
    assert_eq!(sequence(&map("AAAA,CAAA;AAAA")), sequence(&map(";;KAAA")));
    assert_ne!(sequence(&map("AAAA")), sequence(&map("AAAAA")));
    assert_ne!(sequence(&map("AAAA,CAAC")), sequence(&map("AAAC,CAAD")));
}
