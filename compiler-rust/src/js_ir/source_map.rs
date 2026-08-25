//! Source Map v3 generation, ported from `compiler/core/js_source_map.ml`.

use crate::location::Location;
use std::collections::HashMap;
use std::path::{Component, Path, PathBuf};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SourceMapMode {
    #[default]
    None,
    Linked,
    Inline,
    Hidden,
}

#[derive(Debug, Clone)]
struct Source {
    relative_path: String,
    content: Option<String>,
}

#[derive(Debug, Clone, Copy)]
struct Mapping {
    generated_line: usize,
    generated_column: usize,
    source_index: usize,
    original_line: usize,
    original_column: usize,
}

/// Builder installed on one JS printer while one concrete output is rendered.
pub struct SourceMapBuilder {
    generated_file: String,
    generated_dir: PathBuf,
    source_root: String,
    sources_content: bool,
    default_source: PathBuf,
    sources: HashMap<PathBuf, usize>,
    source_list: Vec<Source>,
    mappings: Vec<Mapping>,
    last_generated: Option<(usize, usize)>,
}

impl SourceMapBuilder {
    pub fn new(
        generated_file: &Path,
        default_source: &Path,
        source_root: String,
        sources_content: bool,
    ) -> Self {
        Self {
            generated_file: generated_file
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .into_owned(),
            generated_dir: generated_file
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .to_path_buf(),
            source_root,
            sources_content,
            default_source: default_source.to_path_buf(),
            sources: HashMap::new(),
            source_list: Vec::new(),
            mappings: Vec::new(),
            last_generated: None,
        }
    }

    fn add_source(&mut self) -> (usize, Option<&str>) {
        let filename = absolute_path(&self.default_source);
        if let Some(&index) = self.sources.get(&filename) {
            return (index, self.source_list[index].content.as_deref());
        }
        let content = std::fs::read_to_string(&filename).ok();
        let source = Source {
            relative_path: relative_path(&absolute_path(&self.generated_dir), &filename),
            content,
        };
        let index = self.source_list.len();
        self.source_list.push(source);
        self.sources.insert(filename, index);
        (index, self.source_list[index].content.as_deref())
    }

    pub fn add_mapping(&mut self, generated_line: usize, generated_column: usize, loc: &Location) {
        if loc.loc_ghost || loc.loc_start.cnum < 0 {
            return;
        }
        if self.last_generated == Some((generated_line, generated_column)) {
            return;
        }
        let (source_index, content) = self.add_source();
        let original_line = loc.loc_start.line.saturating_sub(1).max(0) as usize;
        let original_column = match content {
            Some(content) => utf16_units_in_utf8_slice(
                content,
                loc.loc_start.bol.max(0) as usize,
                loc.loc_start.cnum.max(0) as usize,
            ),
            None => loc.loc_start.column().max(0) as usize,
        };
        self.mappings.push(Mapping {
            generated_line,
            generated_column,
            source_index,
            original_line,
            original_column,
        });
        self.last_generated = Some((generated_line, generated_column));
    }

    pub fn json(&self) -> String {
        let sources = self
            .source_list
            .iter()
            .map(|source| serde_json::Value::String(source.relative_path.clone()))
            .collect();
        let mut fields = vec![
            ("version".to_string(), serde_json::Value::from(3)),
            (
                "file".to_string(),
                serde_json::Value::String(self.generated_file.clone()),
            ),
            ("sources".to_string(), serde_json::Value::Array(sources)),
            ("names".to_string(), serde_json::Value::Array(Vec::new())),
            (
                "mappings".to_string(),
                serde_json::Value::String(encode_mappings(&self.mappings)),
            ),
        ];
        if !self.source_root.is_empty() {
            fields.push((
                "sourceRoot".to_string(),
                serde_json::Value::String(self.source_root.clone()),
            ));
        }
        if self.sources_content {
            fields.push((
                "sourcesContent".to_string(),
                serde_json::Value::Array(
                    self.source_list
                        .iter()
                        .map(|source| {
                            source
                                .content
                                .clone()
                                .map_or(serde_json::Value::Null, serde_json::Value::String)
                        })
                        .collect(),
                ),
            ));
        }
        let mut result = String::from("{");
        for (index, (key, value)) in fields.into_iter().enumerate() {
            if index != 0 {
                result.push(',');
            }
            result.push_str(&serde_json::to_string(&key).expect("JSON key"));
            result.push(':');
            result.push_str(&serde_json::to_string(&value).expect("JSON value"));
        }
        result.push('}');
        result
    }
}

fn absolute_path(path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir().unwrap_or_default().join(path)
    }
}

fn normalized_parts(path: &Path) -> Vec<String> {
    path.components()
        .filter_map(|part| match part {
            Component::Prefix(prefix) => {
                Some(prefix.as_os_str().to_string_lossy().replace('\\', "/"))
            }
            Component::RootDir => None,
            Component::Normal(part) => Some(part.to_string_lossy().into_owned()),
            Component::ParentDir => Some("..".to_string()),
            Component::CurDir => None,
        })
        .collect()
}

fn relative_path(from_dir: &Path, to_file: &Path) -> String {
    let from = normalized_parts(from_dir);
    let to = normalized_parts(to_file);
    let common = from.iter().zip(&to).take_while(|(a, b)| a == b).count();
    let mut parts = vec!["..".to_string(); from.len().saturating_sub(common)];
    parts.extend(to.into_iter().skip(common));
    if parts.is_empty() {
        to_file
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .into_owned()
    } else {
        parts.join("/")
    }
}

fn utf16_units_in_utf8_slice(source: &str, start: usize, stop: usize) -> usize {
    let start = start.min(source.len());
    let stop = stop.min(source.len());
    source.get(start..stop).map_or(0, |slice| {
        slice
            .rsplit_once('\n')
            .map_or(slice, |(_, line)| line)
            .encode_utf16()
            .count()
    })
}

const BASE64_VLQ: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

fn add_vlq(output: &mut String, value: isize) {
    let mut value = if value < 0 {
        ((-value) << 1) + 1
    } else {
        value << 1
    } as usize;
    loop {
        let mut digit = value & 31;
        value >>= 5;
        if value > 0 {
            digit |= 32;
        }
        output.push(BASE64_VLQ[digit] as char);
        if value == 0 {
            break;
        }
    }
}

fn encode_mappings(input: &[Mapping]) -> String {
    let mut mappings = input.to_vec();
    mappings.sort_by_key(|mapping| (mapping.generated_line, mapping.generated_column));
    let mut output = String::new();
    let mut current_line = 0;
    let mut previous_generated_column = 0;
    let mut previous_source = 0;
    let mut previous_original_line = 0;
    let mut previous_original_column = 0;
    let mut first_segment = true;
    for mapping in mappings {
        while current_line < mapping.generated_line {
            output.push(';');
            current_line += 1;
            previous_generated_column = 0;
            first_segment = true;
        }
        if !first_segment {
            output.push(',');
        }
        first_segment = false;
        add_vlq(
            &mut output,
            mapping.generated_column as isize - previous_generated_column as isize,
        );
        add_vlq(
            &mut output,
            mapping.source_index as isize - previous_source as isize,
        );
        add_vlq(
            &mut output,
            mapping.original_line as isize - previous_original_line as isize,
        );
        add_vlq(
            &mut output,
            mapping.original_column as isize - previous_original_column as isize,
        );
        previous_generated_column = mapping.generated_column;
        previous_source = mapping.source_index;
        previous_original_line = mapping.original_line;
        previous_original_column = mapping.original_column;
    }
    output
}

pub fn linked_comment(map_file: &Path) -> String {
    format!(
        "//# sourceMappingURL={}\n",
        map_file.file_name().unwrap_or_default().to_string_lossy()
    )
}

pub fn inline_comment(json: &str) -> String {
    format!(
        "//# sourceMappingURL=data:application/json;base64,{}\n",
        base64_encode(json.as_bytes())
    )
}

fn base64_encode(input: &[u8]) -> String {
    let mut output = String::with_capacity(input.len().div_ceil(3) * 4);
    for chunk in input.chunks(3) {
        let b0 = chunk[0] as u32;
        let b1 = chunk.get(1).copied().unwrap_or(0) as u32;
        let b2 = chunk.get(2).copied().unwrap_or(0) as u32;
        let value = (b0 << 16) | (b1 << 8) | b2;
        output.push(BASE64_VLQ[((value >> 18) & 63) as usize] as char);
        output.push(BASE64_VLQ[((value >> 12) & 63) as usize] as char);
        output.push(if chunk.len() > 1 {
            BASE64_VLQ[((value >> 6) & 63) as usize] as char
        } else {
            '='
        });
        output.push(if chunk.len() > 2 {
            BASE64_VLQ[(value & 63) as usize] as char
        } else {
            '='
        });
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encodes_base64_with_padding() {
        assert_eq!(base64_encode(b"f"), "Zg==");
        assert_eq!(base64_encode(b"fo"), "Zm8=");
        assert_eq!(base64_encode(b"foo"), "Zm9v");
    }

    #[test]
    fn encodes_vlq_mappings() {
        assert_eq!(
            encode_mappings(&[Mapping {
                generated_line: 0,
                generated_column: 0,
                source_index: 0,
                original_line: 0,
                original_column: 0
            }]),
            "AAAA"
        );
    }
}
