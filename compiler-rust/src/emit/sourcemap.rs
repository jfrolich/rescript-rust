//! Token coordinates for the opt-in printer. Synthetic rows identify mapping
//! events, not JavaScript source: column zero is a start, columns one and two
//! are end markers. This makes end-token exclusion unambiguous even when two
//! original source locations overlap. Original positions are resolved by the
//! legacy builder, including UTF-16 columns and imported source files.
use super::Unsupported;
use crate::intern::StrIdx;
use crate::js_ir::source_map::{SourceMapBuilder, SourceMapMode, inline_comment, linked_comment};
use crate::lambda::{LamLoc, LamLocTable};
use oxc_span::{SPAN, Span};
use std::{
    cell::RefCell,
    collections::HashMap,
    path::{Path, PathBuf},
    sync::Arc,
};

/// Output metadata shared with the legacy source-map writer.
pub struct Options<'a> {
    /// Generated output file.
    pub target: &'a Path,
    /// Default ReScript source file.
    pub source: &'a Path,
    /// Linked, hidden or inline attachment.
    pub mode: SourceMapMode,
    /// Include original source text in JSON.
    pub sources_content: bool,
    /// Optional sourceRoot URL.
    pub source_root: &'a str,
    /// Location table of the emitted JS arena.
    pub locations: Arc<LamLocTable>,
}

pub(super) struct Spans {
    locations: Arc<LamLocTable>,
    rows: RefCell<Vec<LamLoc>>,
    default_source: PathBuf,
    columns: RefCell<HashMap<StrIdx, Option<Vec<usize>>>>,
    #[cfg(test)]
    operations: std::cell::Cell<usize>,
}
impl Spans {
    pub fn new(locations: Arc<LamLocTable>, default_source: &Path) -> Self {
        Self {
            locations,
            rows: RefCell::new(Vec::new()),
            default_source: default_source.into(),
            columns: RefCell::new(HashMap::new()),
            #[cfg(test)]
            operations: std::cell::Cell::new(0),
        }
    }
    pub fn is_located(&self, loc: Option<LamLoc>) -> bool {
        loc.and_then(|l| self.locations.get(l))
            .is_some_and(|l| !l.loc_ghost && l.loc_start.cnum >= 0)
    }
    pub fn span(&self, loc: Option<LamLoc>) -> Result<Span, Unsupported> {
        #[cfg(test)]
        self.operations.set(self.operations.get() + 1);
        if !self.is_located(loc) {
            return Ok(SPAN);
        }
        let mut rows = self.rows.borrow_mut();
        let start = u32::try_from(rows.len())
            .ok()
            .and_then(|n| n.checked_mul(3))
            .filter(|n| *n <= u32::MAX - 3)
            .ok_or(Unsupported("source map: span capacity"))?;
        rows.push(loc.expect("located mapping"));
        Ok(Span::new(start, start + 2))
    }
    pub fn source_text(&self) -> String {
        "  \n".repeat(self.rows.borrow().len())
    }
    pub fn add_token(
        &self,
        builder: &mut SourceMapBuilder,
        line: u32,
        column: u32,
        generated_line: usize,
        generated_column: usize,
    ) {
        #[cfg(test)]
        self.operations.set(self.operations.get() + 1);
        if column != 0 {
            return;
        }
        let rows = self.rows.borrow();
        let Some(handle) = rows.get(line as usize) else {
            return;
        };
        let loc = self.locations.get(*handle).expect("located span").loc_start;
        let mut columns = self.columns.borrow_mut();
        let index = columns.entry(loc.file_name).or_insert_with(|| {
            let file = self
                .locations
                .file_name(loc.file_name)
                .filter(|s| !s.is_empty() && *s != "_none_")
                .map(Path::new)
                .unwrap_or(&self.default_source);
            std::fs::read_to_string(crate::js_ir::source_map::absolute_path(file))
                .ok()
                .map(|text| utf16_columns(&text))
        });
        let original_column = match index {
            Some(columns) => columns
                .get(loc.cnum.max(0) as usize)
                .copied()
                .unwrap_or_else(|| *columns.last().unwrap()),
            None => loc.column().max(0) as usize,
        };
        builder.add_resolved_mapping(
            generated_line,
            generated_column,
            loc.file_name,
            loc.line.saturating_sub(1).max(0) as usize,
            original_column,
        );
    }
}

// One source-sized allocation, no allocations per token. Indexing by byte
// offset also permits arbitrary order from inlining, not just monotone offsets.
fn utf16_columns(text: &str) -> Vec<usize> {
    let mut columns = vec![0; text.len() + 1];
    let mut column = 0;
    for (offset, ch) in text.char_indices() {
        columns[offset] = column;
        column = if ch == '\n' {
            0
        } else {
            column + ch.len_utf16()
        };
        columns[offset + ch.len_utf8()] = column;
    }
    columns
}

impl Options<'_> {
    pub(super) fn builder(&self) -> SourceMapBuilder {
        SourceMapBuilder::new(
            self.target,
            self.source,
            self.source_root.into(),
            self.sources_content,
        )
        .with_lam_locs(self.locations.clone())
    }
    pub(super) fn attach(
        &self,
        mut code: String,
        builder: SourceMapBuilder,
    ) -> (String, Option<String>) {
        let json = builder.json();
        match self.mode {
            SourceMapMode::Linked => {
                code.push_str(&linked_comment(Path::new(&format!(
                    "{}.map",
                    self.target.display()
                ))));
                (code, Some(json))
            }
            SourceMapMode::Hidden => (code, Some(json)),
            SourceMapMode::Inline => {
                code.push_str(&inline_comment(&json));
                (code, None)
            }
            SourceMapMode::None => (code, None),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        intern::StrIdx,
        location::{Location, Position},
    };
    use std::collections::HashMap;

    #[test]
    fn utf16_columns_index_unicode_and_newlines() {
        let text = "a😀z\n界x";
        let columns = utf16_columns(text);
        assert_eq!(columns[5], 3);
        assert_eq!(columns[7], 0);
        assert_eq!(columns[10], 1);
    }

    #[test]
    fn spans_and_token_rebasing_are_one_row_per_located_node() {
        let mut locations = LamLocTable::located(Arc::new(HashMap::new()));
        let mut handles = Vec::new();
        const N: usize = 100_000;
        for n in 0..N {
            handles.push(locations.intern(Location::from_positions(
                Position::new(StrIdx(0), n as i32 + 1, n as i32 * 3, n as i32 * 3),
                Position::new(StrIdx(0), n as i32 + 1, n as i32 * 3, n as i32 * 3 + 1),
            )));
        }
        let locations = Arc::new(locations);
        let spans = Spans::new(locations.clone(), Path::new("missing.res"));
        let mut builder = SourceMapBuilder::new(
            Path::new("out.js"),
            Path::new("missing.res"),
            String::new(),
            false,
        )
        .with_lam_locs(locations);
        let mut visited = 0;
        for (n, loc) in handles.into_iter().enumerate() {
            let span = spans.span(Some(loc)).unwrap();
            assert_eq!(span.start as usize, n * 3);
            // Start, closing delimiter, postfix: exactly three constant-time
            // dispatches per node, only the first enters the output builder.
            for column in 0..3 {
                spans.add_token(&mut builder, n as u32, column, n, column as usize);
                visited += 1;
            }
        }
        assert_eq!(visited, N * 3);
        assert_eq!(spans.operations.get(), N * 4);
        assert_eq!(spans.rows.borrow().len(), N);
        assert_eq!(spans.source_text().len(), N * 3);
        let json: serde_json::Value = serde_json::from_str(&builder.json()).unwrap();
        assert_eq!(json["mappings"].as_str().unwrap().split(';').count(), N);
        assert!(!json["mappings"].as_str().unwrap().contains(','));
        assert_eq!(spans.span(None).unwrap(), SPAN);
        assert_eq!(spans.span(Some(LamLoc::NONE)).unwrap(), SPAN);
        assert_eq!(spans.rows.borrow().len(), N);
    }
}
