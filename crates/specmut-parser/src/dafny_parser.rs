//! Dafny contract extractor (stub).
//!
//! Phase 7 ships an extractor only — it walks a `.dfy` source line by
//! line, recognises `method`, `function`, and `predicate` declarations,
//! and pulls out their `requires` / `ensures` / `modifies` clauses as
//! *raw strings*.  No Dafny expression is parsed and no FOL translation
//! is attempted; the CLI surfaces the extraction as a summary and prints
//! a "FOL translation requires Boogie integration (not yet implemented)"
//! note.
//!
//! Robust Dafny → FOL would route through Boogie or a real Dafny
//! frontend; the extractor here is a placeholder so downstream tooling
//! can iterate against the same JSON-shape contract used for `.fol`
//! inputs.

use crate::ParseError;

/// Structured extraction output.
#[derive(Debug, Clone)]
pub struct DafnyExtraction {
    /// Discovered `method` declarations.
    pub methods: Vec<DafnyMethod>,
    /// Discovered `function` declarations.
    pub functions: Vec<DafnyFunction>,
    /// Discovered `predicate` declarations.
    pub predicates: Vec<DafnyPredicate>,
    /// Original source, retained so callers can echo a preview.
    pub source: String,
}

/// A Dafny `method`.
#[derive(Debug, Clone)]
pub struct DafnyMethod {
    /// Method name.
    pub name: String,
    /// Parameter list as (name, type) pairs.
    pub params: Vec<(String, String)>,
    /// Return list as (name, type) pairs.
    pub returns: Vec<(String, String)>,
    /// `requires` clauses as raw strings.
    pub requires: Vec<String>,
    /// `ensures` clauses as raw strings.
    pub ensures: Vec<String>,
    /// `modifies` clauses as raw strings.
    pub modifies: Vec<String>,
}

/// A Dafny `function`.
#[derive(Debug, Clone)]
pub struct DafnyFunction {
    /// Function name.
    pub name: String,
    /// Parameter list.
    pub params: Vec<(String, String)>,
    /// Return type.
    pub return_type: String,
    /// `requires` clauses as raw strings.
    pub requires: Vec<String>,
    /// `ensures` clauses as raw strings.
    pub ensures: Vec<String>,
    /// Raw body source between the function declaration's `{` and its
    /// matching `}`.  `None` if the function has no body in the source.
    pub body: Option<String>,
}

/// A Dafny `predicate`.
#[derive(Debug, Clone)]
pub struct DafnyPredicate {
    /// Predicate name.
    pub name: String,
    /// Parameter list.
    pub params: Vec<(String, String)>,
    /// Raw body source.
    pub body: Option<String>,
}

/// The Phase 7 Dafny parser.
#[derive(Debug, Default, Clone, Copy)]
pub struct DafnyParser;

impl DafnyParser {
    /// Extract Dafny declarations from `source`.  Returns an empty
    /// extraction (no error) on input that contains no recognised
    /// declarations.
    pub fn extract(&self, source: &str) -> Result<DafnyExtraction, ParseError> {
        let lines: Vec<&str> = source.lines().collect();
        let mut methods: Vec<DafnyMethod> = Vec::new();
        let mut functions: Vec<DafnyFunction> = Vec::new();
        let mut predicates: Vec<DafnyPredicate> = Vec::new();

        let mut i = 0;
        while i < lines.len() {
            let line = lines[i];
            let trimmed = strip_line_comment(line).trim_start();
            if let Some(rest) = trimmed.strip_prefix("method ") {
                let (m, advance) = parse_method(rest, &lines, i);
                methods.push(m);
                i += advance;
                continue;
            }
            if let Some(rest) = trimmed.strip_prefix("function ") {
                let (f, advance) = parse_function(rest, &lines, i);
                functions.push(f);
                i += advance;
                continue;
            }
            if let Some(rest) = trimmed.strip_prefix("predicate ") {
                let (p, advance) = parse_predicate(rest, &lines, i);
                predicates.push(p);
                i += advance;
                continue;
            }
            i += 1;
        }

        Ok(DafnyExtraction {
            methods,
            functions,
            predicates,
            source: source.to_string(),
        })
    }
}

/// Returns the parsed method and the number of lines to advance past
/// its declaration block.
fn parse_method(after_keyword: &str, lines: &[&str], start: usize) -> (DafnyMethod, usize) {
    let (name, after_name) = take_ident(after_keyword);
    let (params, after_params) = take_paren_list(after_name);
    let returns = if let Some(rest) = strip_keyword(after_params, "returns") {
        take_paren_list(rest).0
    } else {
        String::new()
    };
    let (clauses, advance) = collect_clauses(lines, start);
    let mut method = DafnyMethod {
        name,
        params: split_param_list(&params),
        returns: split_param_list(&returns),
        requires: Vec::new(),
        ensures: Vec::new(),
        modifies: Vec::new(),
    };
    for (kw, text) in clauses {
        match kw.as_str() {
            "requires" => method.requires.push(text),
            "ensures" => method.ensures.push(text),
            "modifies" => method.modifies.push(text),
            _ => {}
        }
    }
    (method, advance)
}

fn parse_function(after_keyword: &str, lines: &[&str], start: usize) -> (DafnyFunction, usize) {
    let (name, after_name) = take_ident(after_keyword);
    let (params, after_params) = take_paren_list(after_name);
    let after_params = after_params.trim_start();
    let return_type = if let Some(rest) = after_params.strip_prefix(':') {
        rest.split_whitespace().next().unwrap_or("").to_string()
    } else {
        String::new()
    };
    let (clauses, advance) = collect_clauses(lines, start);
    let body = collect_body(lines, start);
    let mut function = DafnyFunction {
        name,
        params: split_param_list(&params),
        return_type,
        requires: Vec::new(),
        ensures: Vec::new(),
        body,
    };
    for (kw, text) in clauses {
        match kw.as_str() {
            "requires" => function.requires.push(text),
            "ensures" => function.ensures.push(text),
            _ => {}
        }
    }
    (function, advance)
}

fn parse_predicate(after_keyword: &str, lines: &[&str], start: usize) -> (DafnyPredicate, usize) {
    let (name, after_name) = take_ident(after_keyword);
    let (params, _after_params) = take_paren_list(after_name);
    let body = collect_body(lines, start);
    let advance = body
        .as_ref()
        .map(|b| b.lines().count() + 1)
        .unwrap_or(1);
    (
        DafnyPredicate {
            name,
            params: split_param_list(&params),
            body,
        },
        advance.max(1),
    )
}

fn strip_keyword<'a>(text: &'a str, keyword: &str) -> Option<&'a str> {
    let trimmed = text.trim_start();
    trimmed.strip_prefix(keyword).and_then(|rest| {
        if rest.starts_with(|c: char| c.is_whitespace() || c == '(') {
            Some(rest.trim_start())
        } else {
            None
        }
    })
}

fn strip_line_comment(line: &str) -> &str {
    if let Some(idx) = line.find("//") {
        &line[..idx]
    } else {
        line
    }
}

fn take_ident(s: &str) -> (String, &str) {
    let s = s.trim_start();
    let mut end = 0;
    for c in s.chars() {
        if c.is_alphanumeric() || c == '_' || c == '\'' {
            end += c.len_utf8();
        } else {
            break;
        }
    }
    (s[..end].to_string(), &s[end..])
}

fn take_paren_list(s: &str) -> (String, &str) {
    let s = s.trim_start();
    if !s.starts_with('(') {
        return (String::new(), s);
    }
    let mut depth = 0i32;
    let mut end = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    end = i + c.len_utf8();
                    break;
                }
            }
            _ => {}
        }
    }
    if end == 0 {
        return (String::new(), s);
    }
    (s[1..end - 1].trim().to_string(), &s[end..])
}

fn split_param_list(text: &str) -> Vec<(String, String)> {
    if text.trim().is_empty() {
        return Vec::new();
    }
    text.split(',')
        .filter_map(|piece| {
            let piece = piece.trim();
            if piece.is_empty() {
                return None;
            }
            if let Some(colon) = piece.find(':') {
                let name = piece[..colon].trim().to_string();
                let ty = piece[colon + 1..].trim().to_string();
                Some((name, ty))
            } else {
                Some((String::new(), piece.to_string()))
            }
        })
        .collect()
}

/// Walk lines after `start` looking for `requires` / `ensures` /
/// `modifies` clauses.  Stops at the first line that opens a body (`{`)
/// or begins a new top-level declaration.
fn collect_clauses(lines: &[&str], start: usize) -> (Vec<(String, String)>, usize) {
    let mut out: Vec<(String, String)> = Vec::new();
    let mut advance = 1;
    for line in lines.iter().skip(start + 1) {
        let trimmed = strip_line_comment(line).trim();
        advance += 1;
        if trimmed.is_empty() {
            continue;
        }
        if trimmed.starts_with('{') {
            break;
        }
        if begins_top_level_decl(trimmed) {
            advance -= 1;
            break;
        }
        let clause = trimmed.trim_end_matches(';').trim();
        if let Some(rest) = clause.strip_prefix("requires ") {
            out.push(("requires".to_string(), rest.trim().to_string()));
        } else if let Some(rest) = clause.strip_prefix("ensures ") {
            out.push(("ensures".to_string(), rest.trim().to_string()));
        } else if let Some(rest) = clause.strip_prefix("modifies ") {
            out.push(("modifies".to_string(), rest.trim().to_string()));
        } else {
            continue;
        }
    }
    (out, advance)
}

/// Grab the brace-delimited body following `start`, if present.
fn collect_body(lines: &[&str], start: usize) -> Option<String> {
    let mut body_lines: Vec<String> = Vec::new();
    let mut depth = 0i32;
    let mut in_body = false;
    for line in lines.iter().skip(start) {
        for c in line.chars() {
            match c {
                '{' => {
                    depth += 1;
                    in_body = true;
                }
                '}' => depth -= 1,
                _ => {}
            }
        }
        if in_body {
            body_lines.push((*line).to_string());
            if depth == 0 {
                break;
            }
        }
    }
    if body_lines.is_empty() {
        None
    } else {
        Some(body_lines.join("\n"))
    }
}

fn begins_top_level_decl(line: &str) -> bool {
    ["method ", "function ", "predicate ", "datatype ", "type "]
        .iter()
        .any(|kw| line.starts_with(kw))
}

#[cfg(test)]
mod tests {
    use super::*;

    const INSERTION_SORT: &str = r#"
method InsertionSort(a: array<int>)
  modifies a
  requires a.Length > 0
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  // body omitted
}
"#;

    #[test]
    fn test_parse_method() {
        let ext = DafnyParser.extract(INSERTION_SORT).expect("ok");
        assert_eq!(ext.methods.len(), 1);
        let m = &ext.methods[0];
        assert_eq!(m.name, "InsertionSort");
        assert_eq!(m.params.len(), 1);
        assert_eq!(m.params[0].0, "a");
        assert_eq!(m.requires.len(), 1);
        assert_eq!(m.ensures.len(), 2);
        assert_eq!(m.modifies.len(), 1);
    }

    #[test]
    fn test_parse_function() {
        let src = r#"
function Max(x: int, y: int): int
  requires x >= 0
  ensures Max(x, y) >= x
{
  if x >= y then x else y
}
"#;
        let ext = DafnyParser.extract(src).expect("ok");
        assert_eq!(ext.functions.len(), 1);
        let f = &ext.functions[0];
        assert_eq!(f.name, "Max");
        assert_eq!(f.params.len(), 2);
        assert_eq!(f.return_type, "int");
        assert_eq!(f.requires.len(), 1);
        assert_eq!(f.ensures.len(), 1);
        assert!(f.body.is_some());
    }

    #[test]
    fn test_parse_predicate() {
        let src = "predicate IsSorted(s: seq<int>)\n{ forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] }\n";
        let ext = DafnyParser.extract(src).expect("ok");
        assert_eq!(ext.predicates.len(), 1);
        let p = &ext.predicates[0];
        assert_eq!(p.name, "IsSorted");
        assert_eq!(p.params.len(), 1);
        assert!(p.body.is_some());
    }

    #[test]
    fn test_parse_empty() {
        let ext = DafnyParser.extract("").expect("ok");
        assert!(ext.methods.is_empty());
        assert!(ext.functions.is_empty());
        assert!(ext.predicates.is_empty());
    }

    #[test]
    fn test_parse_multiple_methods() {
        let src = r#"
method A(x: int) ensures x > 0 { }
method B(y: int) requires y >= 0 ensures y >= 0 { }
method C() ensures true { }
"#;
        let ext = DafnyParser.extract(src).expect("ok");
        assert_eq!(ext.methods.len(), 3);
        let names: Vec<&str> = ext.methods.iter().map(|m| m.name.as_str()).collect();
        assert_eq!(names, vec!["A", "B", "C"]);
    }
}
