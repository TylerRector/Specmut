//! Lean 4 surface-syntax extractor.
//!
//! This is a deliberately fragile, regex-flavored line scanner.  Lean's
//! dependent type theory cannot be faithfully translated to FOL without
//! a real elaborator, so this module returns a structured
//! [`LeanExtraction`] rather than a `(Signature, Vec<Formula>)`.  The CLI
//! treats Lean inputs as informational and prints the extraction.
//!
//! What we look for, line by line:
//!
//! * `def Name ... : ... → Prop` (or `-> Prop`) — a predicate.
//! * `def Name (params) : Prop :=` — a predicate with a Prop annotation.
//! * `theorem Name (params) : Conclusion := ...` — a theorem.
//!
//! Predicate names are scanned for the substrings `sort` / `order`
//! ([`PredicateClass::Ordering`]) and `perm`
//! ([`PredicateClass::Permutation`]); anything else is `Other`.

use crate::ParseError;

/// Bundled output of a Lean extraction pass.
#[derive(Debug, Clone)]
pub struct LeanExtraction {
    /// Predicates discovered in the source.
    pub predicates: Vec<LeanPredicate>,
    /// Theorems discovered in the source.
    pub theorems: Vec<LeanTheorem>,
    /// The original source, retained so the CLI can echo a preview.
    pub source: String,
}

/// A `def Name ... : ... → Prop` declaration.
#[derive(Debug, Clone)]
pub struct LeanPredicate {
    /// Predicate name.
    pub name: String,
    /// Best-effort domain types extracted from the parameter list or the
    /// arrow chain before `Prop`.
    pub param_sorts: Vec<String>,
    /// Lines following the definition line until the next top-level
    /// declaration — included for debugging / preview only.
    pub body_lines: Vec<String>,
    /// Heuristic classification.
    pub relation_type: PredicateClass,
}

/// Predicate-name classification heuristic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PredicateClass {
    /// Name contains `sort` or `order`.
    Ordering,
    /// Name contains `perm`.
    Permutation,
    /// Any other name.
    Other,
}

/// A `theorem Name (params) : Conclusion := ...` declaration.
#[derive(Debug, Clone)]
pub struct LeanTheorem {
    /// Theorem name.
    pub name: String,
    /// Best-effort parameter list (text between `(` `)` on the theorem
    /// line).
    pub params: Vec<String>,
    /// Best-effort textual conclusion (between `:` and `:=`).
    pub conclusion: String,
    /// Predicate names that appear textually in the conclusion.
    pub referenced_predicates: Vec<String>,
}

/// Lean parser entry point.
#[derive(Debug, Default, Clone, Copy)]
pub struct LeanParser;

impl LeanParser {
    /// Extract predicates and theorems from `source`.
    pub fn extract(&self, source: &str) -> Result<LeanExtraction, ParseError> {
        let mut predicates: Vec<LeanPredicate> = Vec::new();
        let mut theorems: Vec<LeanTheorem> = Vec::new();

        let lines: Vec<&str> = source.lines().collect();
        for (idx, line) in lines.iter().enumerate() {
            let trimmed = line.trim_start();
            if let Some(pred) = parse_predicate_line(trimmed) {
                let mut pred = pred;
                pred.body_lines = collect_body_lines(&lines, idx);
                predicates.push(pred);
            }
            if let Some(thm) = parse_theorem_line(trimmed) {
                theorems.push(thm);
            }
        }

        // Cross-link theorems to referenced predicates by name match.
        let pred_names: Vec<String> = predicates.iter().map(|p| p.name.clone()).collect();
        for thm in &mut theorems {
            for name in &pred_names {
                if appears_as_word(&thm.conclusion, name) && !thm.referenced_predicates.contains(name) {
                    thm.referenced_predicates.push(name.clone());
                }
            }
        }

        Ok(LeanExtraction {
            predicates,
            theorems,
            source: source.to_string(),
        })
    }
}

fn parse_predicate_line(line: &str) -> Option<LeanPredicate> {
    if !line.starts_with("def ") {
        return None;
    }
    if !(line.contains("→ Prop") || line.contains("-> Prop") || line.contains(": Prop")) {
        return None;
    }
    let rest = &line[4..];
    let name = take_ident(rest)?;
    let after_name = &rest[name.len()..];
    let mut param_sorts = Vec::new();
    // Pull parenthesized parameter list, if any.
    if let Some(paren_open) = after_name.find('(') {
        if let Some(paren_close) = after_name[paren_open + 1..].find(')') {
            let params = &after_name[paren_open + 1..paren_open + 1 + paren_close];
            // Format like "l : List Nat" or "a b : List Nat"; pull the
            // text after the colon as the sort.
            if let Some(colon) = params.find(':') {
                let sort_part = params[colon + 1..].trim();
                param_sorts.push(sort_part.to_string());
            }
        }
    }
    // Also look at the type chain between `:` and `Prop`.
    if let Some(colon) = after_name.find(':') {
        let type_chain = &after_name[colon + 1..];
        let prop_end = type_chain
            .find("→ Prop")
            .or_else(|| type_chain.find("-> Prop"))
            .unwrap_or(type_chain.len());
        let chain = &type_chain[..prop_end];
        for piece in chain.split(['→', '-', '>']) {
            let piece = piece.trim();
            if piece.is_empty() {
                continue;
            }
            if !param_sorts.iter().any(|p| p == piece) {
                param_sorts.push(piece.to_string());
            }
        }
    }

    let relation_type = classify(&name);
    Some(LeanPredicate {
        name,
        param_sorts,
        body_lines: Vec::new(),
        relation_type,
    })
}

fn parse_theorem_line(line: &str) -> Option<LeanTheorem> {
    if !line.starts_with("theorem ") {
        return None;
    }
    let rest = &line[8..];
    let name = take_ident(rest)?;
    let after_name = &rest[name.len()..];
    let mut params = Vec::new();
    let mut cursor = after_name;
    while let Some(open) = cursor.find('(') {
        // Stop scanning params once we hit `:` at top level.
        let pre = &cursor[..open];
        if pre.contains(':') {
            break;
        }
        if let Some(close) = cursor[open + 1..].find(')') {
            let inner = &cursor[open + 1..open + 1 + close];
            params.push(inner.trim().to_string());
            cursor = &cursor[open + 1 + close + 1..];
        } else {
            break;
        }
    }
    let conclusion = extract_conclusion(after_name);
    Some(LeanTheorem {
        name,
        params,
        conclusion,
        referenced_predicates: Vec::new(),
    })
}

fn extract_conclusion(after_name: &str) -> String {
    // Find the colon that introduces the type, skipping colons inside
    // parens (parameter type annotations).
    let mut depth = 0i32;
    let mut colon_idx: Option<usize> = None;
    for (i, c) in after_name.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            ':' if depth == 0 => {
                colon_idx = Some(i);
                break;
            }
            _ => {}
        }
    }
    let Some(colon_idx) = colon_idx else {
        return String::new();
    };
    let after_colon = &after_name[colon_idx + 1..];
    let end = after_colon
        .find(":=")
        .unwrap_or(after_colon.len());
    after_colon[..end].trim().to_string()
}

fn collect_body_lines(lines: &[&str], start: usize) -> Vec<String> {
    let mut out = Vec::new();
    for line in lines.iter().skip(start + 1) {
        let trimmed = line.trim_start();
        if trimmed.starts_with("def ")
            || trimmed.starts_with("theorem ")
            || trimmed.starts_with("axiom ")
        {
            break;
        }
        if trimmed.is_empty() {
            break;
        }
        out.push(line.to_string());
    }
    out
}

fn take_ident(s: &str) -> Option<String> {
    let mut chars = s.chars();
    let first = chars.next()?;
    if !(first.is_alphabetic() || first == '_') {
        return None;
    }
    let mut end = first.len_utf8();
    for c in chars {
        if c.is_alphanumeric() || c == '_' || c == '\'' {
            end += c.len_utf8();
        } else {
            break;
        }
    }
    Some(s[..end].to_string())
}

fn classify(name: &str) -> PredicateClass {
    let lower = name.to_lowercase();
    if lower.contains("perm") {
        PredicateClass::Permutation
    } else if lower.contains("sort") || lower.contains("order") {
        PredicateClass::Ordering
    } else {
        PredicateClass::Other
    }
}

fn appears_as_word(haystack: &str, needle: &str) -> bool {
    let mut idx = 0;
    while let Some(pos) = haystack[idx..].find(needle) {
        let abs = idx + pos;
        let before_ok = abs == 0
            || haystack[..abs]
                .chars()
                .next_back()
                .is_some_and(|c| !c.is_alphanumeric() && c != '_');
        let after_ok = haystack[abs + needle.len()..]
            .chars()
            .next()
            .is_none_or(|c| !c.is_alphanumeric() && c != '_');
        if before_ok && after_ok {
            return true;
        }
        idx = abs + needle.len();
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = r#"
-- A toy Lean source used for testing the extractor.
def Sorted_v1 (l : List Nat) : Prop := ∀ i j, i < j → l[i] ≤ l[j]
def Sorted_v2 (l : List Nat) : Prop := ∀ i, i + 1 < l.length → l[i] ≤ l[i+1]
def Perm_v1 (a b : List Nat) : Prop := ∀ x, a.count x = b.count x
def Perm_v2 (a b : List Nat) : Prop := a.length = b.length ∧ ∀ x, x ∈ a ↔ x ∈ b

theorem insertion_sort_correct : ∀ l, Sorted_v1 (insertionSort l) ∧ Perm_v1 l (insertionSort l) := by sorry
theorem merge_sort_correct : ∀ l, Sorted_v2 (mergeSort l) ∧ Perm_v2 l (mergeSort l) := by sorry
theorem trivial_thm : True := by trivial
"#;

    #[test]
    fn test_extract_predicates() {
        let ext = LeanParser.extract(SAMPLE).expect("ok");
        assert_eq!(ext.predicates.len(), 4);
        let names: Vec<&str> = ext.predicates.iter().map(|p| p.name.as_str()).collect();
        assert!(names.contains(&"Sorted_v1"));
        assert!(names.contains(&"Sorted_v2"));
        assert!(names.contains(&"Perm_v1"));
        assert!(names.contains(&"Perm_v2"));
    }

    #[test]
    fn test_extract_theorems() {
        let ext = LeanParser.extract(SAMPLE).expect("ok");
        assert_eq!(ext.theorems.len(), 3);
        let names: Vec<&str> = ext.theorems.iter().map(|t| t.name.as_str()).collect();
        assert!(names.contains(&"insertion_sort_correct"));
        assert!(names.contains(&"merge_sort_correct"));
        assert!(names.contains(&"trivial_thm"));
        let insertion = ext
            .theorems
            .iter()
            .find(|t| t.name == "insertion_sort_correct")
            .expect("insertion thm");
        assert!(insertion
            .referenced_predicates
            .iter()
            .any(|p| p == "Sorted_v1"));
        assert!(insertion
            .referenced_predicates
            .iter()
            .any(|p| p == "Perm_v1"));
    }

    #[test]
    fn test_predicate_classification() {
        let ext = LeanParser.extract(SAMPLE).expect("ok");
        let sorted = ext
            .predicates
            .iter()
            .find(|p| p.name == "Sorted_v1")
            .expect("Sorted_v1");
        assert_eq!(sorted.relation_type, PredicateClass::Ordering);
        let perm = ext
            .predicates
            .iter()
            .find(|p| p.name == "Perm_v1")
            .expect("Perm_v1");
        assert_eq!(perm.relation_type, PredicateClass::Permutation);
    }

    #[test]
    fn test_empty_input() {
        let ext = LeanParser.extract("").expect("ok");
        assert!(ext.predicates.is_empty());
        assert!(ext.theorems.is_empty());
    }

    #[test]
    fn test_no_match() {
        let src = "-- nothing here\nfn main() {}\nlet x = 1;\n";
        let ext = LeanParser.extract(src).expect("ok");
        assert!(ext.predicates.is_empty());
        assert!(ext.theorems.is_empty());
    }
}
