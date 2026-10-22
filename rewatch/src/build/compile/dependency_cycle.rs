use super::super::build_types::*;
use crate::helpers;
use ahash::AHashSet;
use std::{
    collections::{HashMap, VecDeque},
    path::Path,
};

pub fn find(modules: &Vec<(&String, &Module)>) -> Vec<String> {
    let graph: Vec<(&String, &AHashSet<String>)> = modules
        .iter()
        .map(|(name, module)| (*name, &module.deps))
        .collect();
    find_shortest_cycle(&graph)
}

/// The reported cycle must not depend on hash-map iteration order: start
/// nodes and neighbors are visited in name order, so the same project always
/// reports the same cycle.
fn find_shortest_cycle(modules: &[(&String, &AHashSet<String>)]) -> Vec<String> {
    let mut shortest_cycle: Vec<String> = Vec::new();

    // Build a graph representation for easier traversal, neighbors sorted.
    let mut graph: HashMap<&String, Vec<&String>> = HashMap::new();
    let mut in_degrees: HashMap<&String, usize> = HashMap::new();

    // First pass: collect all nodes and initialize in-degrees
    for (name, _) in modules {
        graph.insert(name, Vec::new());
        in_degrees.insert(name, 0);
    }

    // Second pass: build the graph and count in-degrees
    for (name, deps) in modules {
        // Update in-degrees
        for dep in deps.iter() {
            if let Some(count) = in_degrees.get_mut(dep) {
                *count += 1;
            }
        }

        // Update the graph
        let mut neighbors: Vec<&String> = deps.iter().collect();
        neighbors.sort();
        *graph.get_mut(*name).unwrap() = neighbors;
    }
    // Remove all nodes in the graph that have no outgoing edges
    graph.retain(|_, deps| !deps.is_empty());

    // OPTIMIZATION 1: Start with nodes that are more likely to be in cycles
    // Sort nodes by their connectivity (in-degree + out-degree)
    let mut start_nodes: Vec<&String> = graph.keys().cloned().collect();
    start_nodes.sort_by(|a, b| {
        let a_connectivity = in_degrees.get(a).unwrap_or(&0) + graph.get(a).map_or(0, |v| v.len());
        let b_connectivity = in_degrees.get(b).unwrap_or(&0) + graph.get(b).map_or(0, |v| v.len());
        // Descending connectivity, then by name.
        b_connectivity.cmp(&a_connectivity).then_with(|| a.cmp(b))
    });

    // OPTIMIZATION 2: Keep track of the current shortest cycle length for early termination
    let mut current_shortest_length = usize::MAX;

    // Try BFS from each node to find the shortest cycle
    for start_node in start_nodes {
        // Skip nodes with no incoming edges
        if in_degrees.get(&start_node).is_none_or(|&d| d == 0) {
            continue;
        }

        if let Some(cycle) = find_cycle_bfs(start_node, &graph, current_shortest_length)
            && (shortest_cycle.is_empty() || cycle.len() < shortest_cycle.len())
        {
            current_shortest_length = cycle.len();
            shortest_cycle = cycle;

            // OPTIMIZATION 3: If we find a very short cycle (length <= 3), we
            // stop early; a shorter (2-node) cycle may still exist, so this is
            // the shortest found so far, not necessarily the shortest overall.
            if current_shortest_length <= 3 {
                break;
            }
        }
    }

    shortest_cycle
}

fn find_cycle_bfs<'a>(
    start: &'a String,
    graph: &HashMap<&'a String, Vec<&'a String>>,
    max_length: usize,
) -> Option<Vec<String>> {
    // Use a BFS to find the shortest cycle
    let mut queue: VecDeque<&'a String> = VecDeque::new();
    // Store node -> (distance, parent)
    let mut visited: HashMap<&'a String, (usize, Option<&'a String>)> = HashMap::new();

    // Initialize with start node
    visited.insert(start, (0, None));
    queue.push_back(start);

    while let Some(current) = queue.pop_front() {
        let (dist, _) = visited[current];

        // OPTIMIZATION: Early termination if we've gone too far
        // If we're already at max_length, we won't find a shorter cycle from here
        if dist >= max_length - 1 {
            continue;
        }

        // Check all neighbors
        if let Some(neighbors) = graph.get(current) {
            for &neighbor in neighbors.iter() {
                // If we found the start node again, we have a cycle
                if neighbor == start {
                    // Reconstruct the cycle
                    let mut path = vec![start.clone()];

                    // Backtrack from current to start using parent pointers
                    let mut curr = current;
                    while curr != start {
                        path.push(curr.clone());
                        curr = visited[curr].1.unwrap();
                    }

                    return Some(path);
                }

                // If not visited, add to queue
                if !visited.contains_key(neighbor) {
                    visited.insert(neighbor, (dist + 1, Some(current)));
                    queue.push_back(neighbor);
                }
            }
        }
    }

    None
}

pub fn format(cycle: &[String], build_state: &BuildCommandState) -> String {
    let mut nodes = cycle.to_vec();
    if nodes.is_empty() {
        return String::new();
    }
    nodes.reverse();
    nodes.push(nodes[0].clone());

    let root_path = &build_state.get_root_config().path;
    let root = root_path.parent().unwrap_or(root_path.as_path());

    nodes
        .iter()
        .map(|name| {
            let display_name = helpers::format_namespaced_module_name(name);

            match build_state.get_module(name) {
                Some(Module {
                    source_type: SourceType::SourceFile(source_file),
                    package_name,
                    ..
                }) => {
                    if let Some(package) = build_state.get_package(package_name) {
                        let abs_path = Path::new(&package.path).join(&source_file.implementation.path);
                        let rel_path = abs_path.strip_prefix(root).unwrap_or(&abs_path).to_string_lossy();
                        format!("{display_name} ({rel_path})")
                    } else {
                        display_name
                    }
                }
                Some(Module {
                    source_type: SourceType::MlMap(_),
                    ..
                })
                | None => display_name,
            }
        })
        .collect::<Vec<String>>()
        .join("\n → ")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reports_the_same_cycle_every_time() {
        let names: Vec<String> = ["Cy1", "Cy2", "A"].iter().map(|s| s.to_string()).collect();
        let deps: Vec<AHashSet<String>> = vec![
            AHashSet::from(["Cy2".to_string()]),
            AHashSet::from(["Cy1".to_string()]),
            AHashSet::from(["Cy1".to_string()]),
        ];
        let graph: Vec<(&String, &AHashSet<String>)> = names.iter().zip(deps.iter()).collect();
        let expected = find_shortest_cycle(&graph);
        assert_eq!(expected, vec!["Cy1".to_string(), "Cy2".to_string()]);
        // Hash maps seed their order per instance: rebuilding them must not
        // change the answer, whatever the input order.
        for _ in 0..50 {
            let mut reversed = graph.clone();
            reversed.reverse();
            assert_eq!(find_shortest_cycle(&graph), expected);
            assert_eq!(find_shortest_cycle(&reversed), expected);
        }
    }
}
