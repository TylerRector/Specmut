//! Parser for the `.model` implementation file format (§7.2 option A).
//!
//! ```text
//! model Elem = {a, b}.
//! leq(a, a) = true.
//! func_name(a) = b.
//! ```

use std::collections::{BTreeMap, BTreeSet};

use specmut_core::model::FiniteModel;
use specmut_core::signature::{Signature, SortSymbol};
use thiserror::Error;

/// Errors raised while parsing a `.model` file.
#[derive(Debug, Error)]
pub enum ModelParseError {
    /// Unrecognized line shape.
    #[error("syntax error on line {line}: {message}")]
    Syntax {
        /// 1-based line number.
        line: usize,
        /// Human-readable description.
        message: String,
    },
    /// A line references an element not declared in the `model ... = {...}` header.
    #[error("unknown element '{name}' on line {line}")]
    UnknownElement {
        /// 1-based line number.
        line: usize,
        /// The undeclared identifier.
        name: String,
    },
    /// A line references a symbol not present in the signature.
    #[error("unknown {kind} '{name}' on line {line}")]
    UnknownSymbol {
        /// 1-based line number.
        line: usize,
        /// `"relation"` or `"function"`.
        kind: String,
        /// The undeclared name.
        name: String,
    },
    /// No `model` header found.
    #[error("missing 'model SortName = {{...}}.' header")]
    MissingHeader,
}

/// Parse a `.model` source into a [`FiniteModel`] consistent with `sig`.
///
/// `sig` provides the sort / function / relation symbols; the file body
/// supplies their interpretations.  Element names are mapped to carrier
/// indices in the order they appear in the model header (e.g.
/// `{a, b, c}` → 0, 1, 2).
pub fn parse_model_file(source: &str, sig: &Signature) -> Result<FiniteModel, ModelParseError> {
    let lines: Vec<(usize, String)> = source
        .lines()
        .enumerate()
        .map(|(i, l)| (i + 1, strip_comment(l).trim().to_string()))
        .filter(|(_, l)| !l.is_empty())
        .collect();

    let mut carriers: BTreeMap<SortSymbol, usize> = BTreeMap::new();
    let mut elements: BTreeMap<String, usize> = BTreeMap::new();
    let mut function_interps: BTreeMap<String, BTreeMap<Vec<usize>, usize>> = BTreeMap::new();
    let mut relation_interps: BTreeMap<String, BTreeSet<Vec<usize>>> = BTreeMap::new();
    for r in &sig.relations {
        relation_interps.insert(r.name.clone(), BTreeSet::new());
    }

    let mut header_seen = false;
    for (line_no, raw) in &lines {
        let stripped = raw.trim_end_matches('.');
        if let Some(rest) = stripped.strip_prefix("model ") {
            // `model Sort = {e1, e2, ...}` header.
            let (sort_name, elements_text) =
                rest.split_once('=').ok_or_else(|| ModelParseError::Syntax {
                    line: *line_no,
                    message: "expected '=' in model header".to_string(),
                })?;
            let sort_name = sort_name.trim().to_string();
            let elements_text = elements_text.trim();
            let inner = elements_text
                .strip_prefix('{')
                .and_then(|s| s.strip_suffix('}'))
                .ok_or_else(|| ModelParseError::Syntax {
                    line: *line_no,
                    message: "expected '{...}' in model header".to_string(),
                })?;
            let names: Vec<String> = inner
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            let sort_sym = SortSymbol::new(&sort_name);
            if !sig.sorts.contains(&sort_sym) {
                return Err(ModelParseError::UnknownSymbol {
                    line: *line_no,
                    kind: "sort".to_string(),
                    name: sort_name,
                });
            }
            for (idx, name) in names.iter().enumerate() {
                elements.insert(name.clone(), idx);
            }
            carriers.insert(sort_sym, names.len());
            header_seen = true;
            continue;
        }

        if !header_seen {
            return Err(ModelParseError::MissingHeader);
        }

        // Body line: `name(args) = value` or `name = value` (zero-arity).
        let (lhs, rhs) = stripped.split_once('=').ok_or_else(|| ModelParseError::Syntax {
            line: *line_no,
            message: "expected '=' in body line".to_string(),
        })?;
        let lhs = lhs.trim();
        let rhs = rhs.trim();
        let (name, args_text) = if let Some(open) = lhs.find('(') {
            let close = lhs.rfind(')').ok_or_else(|| ModelParseError::Syntax {
                line: *line_no,
                message: "missing ')'".to_string(),
            })?;
            (lhs[..open].trim().to_string(), lhs[open + 1..close].to_string())
        } else {
            (lhs.to_string(), String::new())
        };
        let arg_names: Vec<String> = if args_text.trim().is_empty() {
            Vec::new()
        } else {
            args_text
                .split(',')
                .map(|s| s.trim().to_string())
                .collect()
        };
        let arg_indices: Result<Vec<usize>, ModelParseError> = arg_names
            .iter()
            .map(|n| {
                elements
                    .get(n)
                    .copied()
                    .ok_or_else(|| ModelParseError::UnknownElement {
                        line: *line_no,
                        name: n.clone(),
                    })
            })
            .collect();
        let arg_indices = arg_indices?;

        // Relation interpretation or function interpretation?
        if let Some(_r) = sig.relations.iter().find(|r| r.name == name) {
            let truthy = rhs == "true";
            if truthy {
                relation_interps
                    .entry(name.clone())
                    .or_default()
                    .insert(arg_indices);
            } // false is implicit
        } else if let Some(_f) = sig.functions.iter().find(|f| f.name == name) {
            let value = elements
                .get(rhs)
                .copied()
                .ok_or_else(|| ModelParseError::UnknownElement {
                    line: *line_no,
                    name: rhs.to_string(),
                })?;
            function_interps
                .entry(name.clone())
                .or_default()
                .insert(arg_indices, value);
        } else {
            return Err(ModelParseError::UnknownSymbol {
                line: *line_no,
                kind: "symbol".to_string(),
                name,
            });
        }
    }

    if !header_seen {
        return Err(ModelParseError::MissingHeader);
    }

    Ok(FiniteModel {
        signature: sig.clone(),
        carriers,
        function_interps,
        relation_interps,
    })
}

fn strip_comment(line: &str) -> &str {
    if let Some(idx) = line.find("--") {
        &line[..idx]
    } else {
        line
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use specmut_core::signature::{FunctionSymbol, RelationSymbol};

    fn sig() -> Signature {
        let e = SortSymbol::new("Elem");
        Signature::new(
            vec![e.clone()],
            vec![FunctionSymbol::new("output", vec![e.clone()], e.clone())],
            vec![RelationSymbol::new("leq", vec![e.clone(), e.clone()])],
        )
        .expect("valid")
    }

    #[test]
    fn parses_minimal_model() {
        let src = "model Elem = {a, b}.\nleq(a, a) = true.\nleq(a, b) = true.\nleq(b, a) = false.\nleq(b, b) = true.\noutput(a) = a.\noutput(b) = b.\n";
        let model = parse_model_file(src, &sig()).expect("ok");
        assert_eq!(model.carriers.get(&SortSymbol::new("Elem")), Some(&2));
        let leq = model.relation_interps.get("leq").expect("leq");
        assert!(leq.contains(&vec![0, 1]));
        assert!(!leq.contains(&vec![1, 0]));
    }

    #[test]
    fn rejects_missing_header() {
        let src = "leq(a, a) = true.\n";
        assert!(parse_model_file(src, &sig()).is_err());
    }

    #[test]
    fn rejects_unknown_element() {
        let src = "model Elem = {a, b}.\nleq(a, z) = true.\n";
        assert!(matches!(
            parse_model_file(src, &sig()),
            Err(ModelParseError::UnknownElement { .. })
        ));
    }
}
