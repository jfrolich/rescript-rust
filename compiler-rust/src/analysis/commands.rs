//! Commands on a typed module: a port of the matching parts of
//! analysis/src/commands.ml and cli.ml.

use super::json::Json;
use super::references;
use super::session::{Loaded, ProjectSession};
use super::shared_types::{Loc, LocType, Pos};
use super::uri::UriStyle;
use super::Output;

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
    let is_module = matches!(loc_item.loc_type, LocType::LModule(_) | LocType::TopLevelModule(_));
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
    let mut locations: Vec<Json> = references::all_references_for_loc_item(session, full, &loc_item)
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
            let is_module = matches!(loc_item.loc_type, LocType::LModule(_) | LocType::TopLevelModule(_));
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
        Json::assoc([("kind", Json::String("markdown".to_string())), ("value", Json::String(value))]),
    )]))
}
