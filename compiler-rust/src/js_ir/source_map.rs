//! Source Map v3 generation, ported from `compiler/core/js_source_map.ml`.

use crate::intern::StrIdx;
use crate::lambda::{LamLoc, LamLocTable};
use std::collections::HashMap;
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

/// Whether a source map is produced and how the JavaScript refers to it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SourceMapMode {
    /// No source map.
    #[default]
    None,
    /// A `.map` file next to the output, named by a `sourceMappingURL` comment.
    Linked,
    /// The map embedded in the output as a base64 `data:` URL.
    Inline,
    /// A `.map` file with no `sourceMappingURL` comment in the output.
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
    /// Absolute directory of the generated file.
    generated_dir: PathBuf,
    source_root: String,
    sources_content: bool,
    default_source: PathBuf,
    /// Resolves the JS IR location handles and their source file names.
    lam_locs: Arc<LamLocTable>,
    sources: HashMap<PathBuf, usize>,
    /// `sources` index already resolved for a location's file-name index.
    sources_by_file_name: HashMap<StrIdx, usize>,
    source_list: Vec<Source>,
    mappings: Vec<Mapping>,
    last_generated: Option<(usize, usize)>,
}

impl SourceMapBuilder {
    /// A builder for the map of `generated_file`; locations without a usable file
    /// name map to `default_source`. `sources_content` embeds each source's text.
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
            generated_dir: absolute_path(generated_file.parent().unwrap_or_else(|| Path::new("."))),
            source_root,
            sources_content,
            default_source: default_source.to_path_buf(),
            lam_locs: Arc::new(LamLocTable::opaque()),
            sources: HashMap::new(),
            sources_by_file_name: HashMap::new(),
            source_list: Vec::new(),
            mappings: Vec::new(),
            last_generated: None,
        }
    }

    /// Use `lam_locs` to resolve the location handles passed to [`Self::add_mapping`].
    pub fn with_lam_locs(mut self, lam_locs: Arc<LamLocTable>) -> Self {
        self.lam_locs = lam_locs;
        self
    }

    fn add_source(&mut self, source_file_name: StrIdx) -> (usize, Option<&str>) {
        if let Some(&index) = self.sources_by_file_name.get(&source_file_name) {
            return (index, self.source_list[index].content.as_deref());
        }
        let index = self.resolve_source(source_file_name);
        self.sources_by_file_name.insert(source_file_name, index);
        (index, self.source_list[index].content.as_deref())
    }

    fn resolve_source(&mut self, source_file_name: StrIdx) -> usize {
        let source_file = self
            .lam_locs
            .file_name(source_file_name)
            .filter(|name| !name.is_empty() && *name != "_none_")
            .map(Path::new)
            .unwrap_or(&self.default_source);
        let filename = absolute_path(source_file);
        if let Some(&index) = self.sources.get(&filename) {
            return index;
        }
        let content = std::fs::read_to_string(&filename).ok();
        let source = Source {
            relative_path: relative_path(&self.generated_dir, &filename),
            content,
        };
        let index = self.source_list.len();
        self.source_list.push(source);
        self.sources.insert(filename, index);
        index
    }

    /// Map the generated position (zero-based line and UTF-16 column) to the
    /// start of `loc`. Ghost locations and repeats of the previous position are skipped.
    pub fn add_mapping(&mut self, generated_line: usize, generated_column: usize, loc: &LamLoc) {
        let Some(loc) = self.lam_locs.get(*loc) else {
            return;
        };
        if loc.loc_ghost || loc.loc_start.cnum < 0 {
            return;
        }
        if self.last_generated == Some((generated_line, generated_column)) {
            return;
        }
        let (source_index, content) = self.add_source(loc.loc_start.file_name);
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

    /// The Source Map v3 JSON for the mappings added so far.
    pub fn json(&self) -> String {
        fn push_json_str(result: &mut String, value: &str) {
            result.push_str(&serde_json::to_string(value).expect("JSON string"));
        }
        fn push_key(result: &mut String, key: &str) {
            if result.len() > 1 {
                result.push(',');
            }
            push_json_str(result, key);
            result.push(':');
        }

        let mut result = String::from("{");
        push_key(&mut result, "version");
        result.push('3');
        push_key(&mut result, "file");
        push_json_str(&mut result, &self.generated_file);
        push_key(&mut result, "sources");
        result.push('[');
        for (index, source) in self.source_list.iter().enumerate() {
            if index != 0 {
                result.push(',');
            }
            push_json_str(&mut result, &source.relative_path);
        }
        result.push(']');
        push_key(&mut result, "names");
        result.push_str("[]");
        push_key(&mut result, "mappings");
        push_json_str(&mut result, &encode_mappings(&self.mappings));
        if !self.source_root.is_empty() {
            push_key(&mut result, "sourceRoot");
            push_json_str(&mut result, &self.source_root);
        }
        if self.sources_content {
            push_key(&mut result, "sourcesContent");
            result.push('[');
            for (index, source) in self.source_list.iter().enumerate() {
                if index != 0 {
                    result.push(',');
                }
                match &source.content {
                    Some(content) => push_json_str(&mut result, content),
                    None => result.push_str("null"),
                }
            }
            result.push(']');
        }
        result.push('}');
        result
    }
}

fn has_windows_drive(path: &Path) -> bool {
    let rendered = path.to_string_lossy();
    rendered.as_bytes().get(1) == Some(&b':')
        && rendered
            .as_bytes()
            .first()
            .is_some_and(u8::is_ascii_alphabetic)
}

fn absolute_path(path: &Path) -> PathBuf {
    if path.is_absolute() || has_windows_drive(path) {
        path.to_path_buf()
    } else {
        crate::process_cwd::current_dir()
            .unwrap_or_else(|_| Path::new(""))
            .join(path)
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

fn drive_root(parts: &[String]) -> Option<String> {
    parts
        .first()
        .filter(|part| part.len() == 2 && part.ends_with(':'))
        .map(|part| part.to_ascii_uppercase())
}

fn slash_normalized(path: &Path) -> String {
    path.to_string_lossy().replace('\\', "/")
}

fn relative_path(from_dir: &Path, to_file: &Path) -> String {
    let from = normalized_parts(&absolute_path(from_dir));
    let to_absolute = absolute_path(to_file);
    let to = normalized_parts(&to_absolute);
    match (drive_root(&from), drive_root(&to)) {
        (Some(from_drive), Some(to_drive)) if from_drive != to_drive => {
            return slash_normalized(&to_absolute);
        }
        (Some(_), None) | (None, Some(_)) => return slash_normalized(&to_absolute),
        _ => {}
    }
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

/// The `sourceMappingURL` comment pointing at `map_file` by its file name.
pub fn linked_comment(map_file: &Path) -> String {
    format!(
        "//# sourceMappingURL={}\n",
        map_file.file_name().unwrap_or_default().to_string_lossy()
    )
}

/// The `sourceMappingURL` comment embedding the map `json` as a base64 data URL.
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
    fn json_keeps_the_fixed_key_order() {
        let builder = SourceMapBuilder::new(
            Path::new("/out/x.js"),
            Path::new("/src/x.res"),
            "root\"".to_string(),
            true,
        );
        assert_eq!(
            builder.json(),
            r#"{"version":3,"file":"x.js","sources":[],"names":[],"mappings":"","sourceRoot":"root\"","sourcesContent":[]}"#
        );
        let builder = SourceMapBuilder::new(
            Path::new("/out/x.js"),
            Path::new("/src/x.res"),
            String::new(),
            false,
        );
        assert_eq!(
            builder.json(),
            r#"{"version":3,"file":"x.js","sources":[],"names":[],"mappings":""}"#
        );
    }

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

    #[test]
    fn records_the_source_file_from_each_mapping() {
        use crate::location::{Location, Position};

        let first = StrIdx(1);
        let second = StrIdx(2);
        let mut lam_locs = LamLocTable::located(Arc::new(HashMap::from([
            (first, "/project/src/first.res".to_string()),
            (second, "/project/generated/second.res".to_string()),
        ])));
        let first_loc = lam_locs.intern(Location::from_positions(
            Position::new(first, 1, 0, 0),
            Position::new(first, 1, 0, 1),
        ));
        let second_loc = lam_locs.intern(Location::from_positions(
            Position::new(second, 1, 0, 0),
            Position::new(second, 1, 0, 1),
        ));
        let mut builder = SourceMapBuilder::new(
            Path::new("/project/lib/app.js"),
            Path::new("/project/src/default.res"),
            String::new(),
            false,
        )
        .with_lam_locs(Arc::new(lam_locs));
        builder.add_mapping(0, 0, &first_loc);
        builder.add_mapping(1, 0, &second_loc);

        let json: serde_json::Value = serde_json::from_str(&builder.json()).unwrap();
        assert_eq!(
            json["sources"],
            serde_json::json!(["../src/first.res", "../generated/second.res"])
        );
    }

    #[test]
    fn keeps_cross_drive_windows_source_paths_absolute() {
        assert_eq!(
            relative_path(Path::new("C:/project/lib"), Path::new("D:/src/input.res")),
            "D:/src/input.res"
        );
    }
}
