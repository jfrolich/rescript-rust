//! Commands on a typed module: a port of the matching parts of
//! analysis/src/commands.ml and cli.ml.

use super::Output;
use super::json::Json;
use super::references;
use super::session::{Loaded, ProjectSession};
use super::shared_types::{Loc, LocType, Pos};
use super::uri::UriStyle;

/// `Lsp.Types.Location.yojson_of_t`.
fn location_json(uri: String, loc: &Loc) -> Json {
    Json::assoc([("range", loc.range().to_json()), ("uri", Json::String(uri))])
}

/// `Commands.definition`.
pub fn definition(
    session: &ProjectSession<'_>,
    style: UriStyle,
    full: Option<&Loaded>,
    pos: (i32, i32),
    debug: bool,
    out: &mut Output,
) -> Option<Json> {
    let full = full?;
    let loc_item = references::get_loc_item(full, pos, debug, out)?;
    let (uri, loc) = references::definition_for_loc_item(session, full, &loc_item)?;
    if loc.ghost {
        return None;
    }
    let is_interface = super::uri::is_interface(&full.file.uri);
    let pos_is_zero = |p: &Pos| p.line == 1 && p.cnum - p.bol == 0;
    let is_module = matches!(
        loc_item.loc_type,
        LocType::LModule(_) | LocType::TopLevelModule(_)
    );
    let skip_loc = !is_module && !is_interface && pos_is_zero(&loc.start) && pos_is_zero(&loc.end);
    if skip_loc {
        None
    } else {
        Some(location_json(style.canonical_lsp_string(&uri), &loc))
    }
}

/// `Commands.type_definition`.
pub fn type_definition(
    session: &ProjectSession<'_>,
    style: UriStyle,
    full: Option<&Loaded>,
    pos: (i32, i32),
    debug: bool,
    out: &mut Output,
) -> Option<Json> {
    let full = full?;
    let loc_item = references::get_loc_item(full, pos, debug, out)?;
    let (uri, loc) = references::type_definition_for_loc_item(session, full, &loc_item)?;
    Some(location_json(style.canonical_lsp_string(&uri), &loc))
}

/// `Commands.references`, in its (reversed) order.
pub fn references(
    session: &ProjectSession<'_>,
    style: UriStyle,
    full: Option<&Loaded>,
    pos: (i32, i32),
    debug: bool,
    out: &mut Output,
) -> Vec<Json> {
    let Some(full) = full else {
        return Vec::new();
    };
    let Some(loc_item) = references::get_loc_item(full, pos, debug, out) else {
        return Vec::new();
    };
    let mut locations: Vec<Json> =
        references::all_references_for_loc_item(session, full, &loc_item)
            .into_iter()
            .map(|r| {
                let loc = r.loc.unwrap_or_else(references::top_level_loc);
                location_json(style.lsp_string(&r.uri), &loc)
            })
            .collect();
    locations.reverse();
    locations
}

/// `Commands.hover`. Hovering where no item is located goes through
/// completion, which is not ported yet.
pub fn hover(
    session: &ProjectSession<'_>,
    style: UriStyle,
    full: Option<&Loaded>,
    pos: (i32, i32),
    supports_markdown_links: bool,
    debug: bool,
    out: &mut Output,
) -> Option<Json> {
    let full = full?;
    let value = match references::get_loc_item(full, pos, debug, out) {
        None => {
            if debug {
                out.print("Nothing at that position. Now trying to use completion.\n");
            }
            None
        }
        Some(loc_item) => {
            let is_module = matches!(
                loc_item.loc_type,
                LocType::LModule(_) | LocType::TopLevelModule(_)
            );
            let skip_zero = match references::definition_for_loc_item(session, full, &loc_item) {
                None => false,
                Some((_, loc)) => {
                    let is_interface = super::uri::is_interface(&full.file.uri);
                    let pos_is_zero = |p: &Pos| !is_interface && p.line == 1 && p.cnum - p.bol == 0;
                    !is_module && pos_is_zero(&loc.start) && pos_is_zero(&loc.end)
                }
            };
            if skip_zero {
                None
            } else {
                super::hover::Hover {
                    session,
                    style,
                    supports_markdown_links,
                }
                .new_hover(full, &loc_item)
            }
        }
    }?;
    Some(Json::assoc([(
        "contents",
        Json::assoc([
            ("kind", Json::String("markdown".to_string())),
            ("value", Json::String(value)),
        ]),
    )]))
}

/// `Filename.dirname` (POSIX).
fn dirname(path: &str) -> String {
    let trimmed = path.trim_end_matches('/');
    if trimmed.is_empty() {
        return if path.is_empty() {
            ".".to_string()
        } else {
            "/".to_string()
        };
    }
    match trimmed.rfind('/') {
        None => ".".to_string(),
        Some(i) => {
            let dir = trimmed[..i].trim_end_matches('/');
            if dir.is_empty() {
                "/".to_string()
            } else {
                dir.to_string()
            }
        }
    }
}

/// `Filename.extension`.
fn extension(path: &str) -> &str {
    let base = path.rsplit('/').next().unwrap_or(path);
    let stripped = base.trim_start_matches('.');
    match stripped.rfind('.') {
        Some(i) => &stripped[i..],
        None => "",
    }
}

/// `Filename.concat`.
fn concat(dir: &str, file: &str) -> String {
    if dir.is_empty() || dir.ends_with('/') {
        format!("{dir}{file}")
    } else {
        format!("{dir}/{file}")
    }
}

/// `Commands.rename`: the document changes, or `None`.
pub fn rename(
    session: &ProjectSession<'_>,
    style: UriStyle,
    full: Option<&Loaded>,
    pos: (i32, i32),
    new_name: &str,
    debug: bool,
    out: &mut Output,
) -> Option<Vec<Json>> {
    let full = full?;
    let loc_item = references::get_loc_item(full, pos, debug, out)?;
    let all_references = references::all_references_for_loc_item(session, full, &loc_item);
    let file_renames = all_references.iter().filter(|r| r.loc.is_none()).map(|r| {
        let path = style.to_path(&r.uri);
        let dir = match dirname(&path).as_str() {
            "." => String::new(),
            other => other.to_string(),
        };
        let new_path = concat(&dir, &format!("{new_name}{}", extension(&path)));
        Json::assoc([
            ("kind", Json::String("rename".to_string())),
            (
                "newUri",
                Json::String(style.lsp_string_of_path_string(&new_path)),
            ),
            ("oldUri", Json::String(style.lsp_string(&r.uri))),
        ])
    });
    // `String_map`: by URI; each URI's edits in reverse; the fold conses, so
    // the URIs come out in descending order.
    let mut edits_by_uri: std::collections::BTreeMap<String, Vec<Json>> =
        std::collections::BTreeMap::new();
    for r in &all_references {
        let Some(loc) = r.loc else {
            continue;
        };
        let edit = Json::assoc([
            ("newText", Json::String(new_name.to_string())),
            ("range", loc.range().to_json()),
        ]);
        edits_by_uri
            .entry(style.to_string(&r.uri))
            .or_default()
            .push(edit);
    }
    let text_document_edits = edits_by_uri.into_iter().rev().map(|(uri, edits)| {
        Json::assoc([
            ("edits", Json::List(edits.into_iter().rev().collect())),
            (
                "textDocument",
                Json::assoc([
                    (
                        "uri",
                        Json::String(super::uri::to_lsp_string(&super::uri::of_string(&uri))),
                    ),
                    ("version", Json::Int(0)),
                ]),
            ),
        ])
    });
    Some(file_renames.chain(text_document_edits).collect())
}

/// `Commands.prepare_rename`, as `Cli.prepare_rename` prints it.
pub fn prepare_rename(
    full: Option<&Loaded>,
    pos: (i32, i32),
    debug: bool,
    out: &mut Output,
) -> Option<Json> {
    let full = full?;
    let loc_item = references::get_loc_item(full, pos, debug, out)?;
    let range = loc_item.loc.range().to_json();
    match &loc_item.loc_type {
        LocType::Typed(name, _, _)
        | LocType::TopLevelModule(name)
        | LocType::TypeDefinition(name, _, _) => Some(Json::assoc([
            ("range", range),
            ("placeholder", Json::String(name.clone())),
        ])),
        _ => Some(range),
    }
}
