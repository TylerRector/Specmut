//! Serde-shaped IR matching the JSON the Phase A exporter produces.

use serde::Deserialize;

/// Top-level document deserialized from the exporter's stdout JSON.
#[derive(Debug, Clone, Deserialize)]
pub struct LeanIR {
    /// IR schema version (currently 1).  Optional so older fixtures still load.
    #[serde(default)]
    pub version: Option<u32>,
    /// Source file path the exporter was run on.
    #[serde(default)]
    pub source_file: Option<String>,
    /// Inductive sorts declared in the source.
    #[serde(default)]
    pub sorts: Vec<IRSort>,
    /// Data constructors of those inductives.
    #[serde(default)]
    pub constructors: Vec<IRConstructor>,
    /// Total / partial function definitions.
    #[serde(default)]
    pub functions: Vec<IRFunction>,
    /// Predicate (Prop-valued) definitions.
    #[serde(default)]
    pub predicates: Vec<IRPredicate>,
    /// Theorems declared in the source.
    #[serde(default)]
    pub theorems: Vec<IRTheorem>,
    /// Elaboration errors / non-fatal issues echoed by the exporter.
    #[serde(default)]
    pub warnings: Vec<String>,
}

/// Inductive sort declaration.  `kind` is `"inductive"` for now.
#[derive(Debug, Clone, Deserialize)]
pub struct IRSort {
    /// Sort name (potentially mangled for parameterized types).
    pub name: String,
    /// Sort kind.  Currently always `"inductive"`.
    pub kind: String,
    /// Number of type parameters on the inductive.
    #[serde(default, rename = "num_params")]
    pub num_params: Option<u32>,
    /// Number of constructors.
    #[serde(default, rename = "num_ctors")]
    pub num_ctors: Option<u32>,
}

/// Data constructor for some `IRSort`.
#[derive(Debug, Clone, Deserialize)]
pub struct IRConstructor {
    /// Constructor name (e.g. `Tree.leaf`).
    pub name: String,
    /// Parent inductive sort.
    pub sort: String,
    /// Field sort names in order.
    #[serde(default)]
    pub fields: Vec<String>,
}

/// Function (non-Prop-valued definition).
#[derive(Debug, Clone, Deserialize)]
pub struct IRFunction {
    /// Function name.
    pub name: String,
    /// Domain sorts in order.
    #[serde(default)]
    pub domain: Vec<String>,
    /// Codomain sort.
    pub codomain: String,
    /// Equation lemmas (for recursive defs).  Empty for non-recursive functions.
    #[serde(default)]
    pub equations: Vec<IREquation>,
}

/// Predicate (Prop-valued definition).
#[derive(Debug, Clone, Deserialize)]
pub struct IRPredicate {
    /// Predicate name.
    pub name: String,
    /// Predicate parameters with their sorts.
    #[serde(default)]
    pub params: Vec<IRParam>,
    /// The predicate body as an IR expression.  For recursive predicates this
    /// is typically a `brecOn`-shaped tree the consumer should ignore in
    /// favour of `equations`.
    pub body: IRExpr,
    /// Equation lemmas harvested by Phase A's M4 pass.
    #[serde(default)]
    pub equations: Vec<IREquation>,
}

/// A single binder: name + sort.
#[derive(Debug, Clone, Deserialize)]
pub struct IRParam {
    /// Binder name (or `_` if anonymous / hygienic).
    pub name: String,
    /// Binder sort identifier.
    pub sort: String,
}

/// A pattern-match equation lemma: `∀ vars, lhs = rhs`.
#[derive(Debug, Clone, Deserialize)]
pub struct IREquation {
    /// Universally-bound variables.
    #[serde(default)]
    pub vars: Vec<IRParam>,
    /// LHS expression (typically a predicate application against a constructor pattern).
    pub lhs: IRExpr,
    /// RHS expression.
    pub rhs: IRExpr,
}

/// Theorem statement.
#[derive(Debug, Clone, Deserialize)]
pub struct IRTheorem {
    /// Theorem name.
    pub name: String,
    /// Leading Prop-typed binders split off the front of the forall-chain.
    #[serde(default)]
    pub hypotheses: Vec<IRHypothesis>,
    /// The remaining conclusion expression.
    pub conclusion: IRExpr,
}

/// Hypothesis representation, tolerant of two shapes:
///   * a bare `IRExpr` (current Phase A output);
///   * an object `{name, body}` (current Phase A M4 output).
#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
pub enum IRHypothesis {
    /// Object form `{name, body}` emitted by Phase A.
    Named {
        /// Hypothesis identifier (or `_` for anonymous).
        name: String,
        /// The propositional body.
        body: IRExpr,
    },
    /// Bare proposition form (no name).
    Expr(IRExpr),
}

impl IRHypothesis {
    /// Project to the underlying expression regardless of shape.
    pub fn body(&self) -> &IRExpr {
        match self {
            IRHypothesis::Expr(e) => e,
            IRHypothesis::Named { body, .. } => body,
        }
    }
}

/// Discriminated union of IR expression nodes.
///
/// `kind` is the serde tag; field names are stable across Phase A versions.
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind")]
pub enum IRExpr {
    /// Bound or free variable reference by name.
    #[serde(rename = "var")]
    Var {
        /// Variable identifier matched against the surrounding binder stack.
        name: String,
    },

    /// Named function application.  `args` may be empty for nullary constants.
    #[serde(rename = "app")]
    App {
        /// Function or predicate name.
        #[serde(rename = "fn")]
        fn_name: String,
        /// Argument expressions in order.
        #[serde(default)]
        args: Vec<IRExpr>,
    },

    /// ∀ var:sort, body.
    #[serde(rename = "forall")]
    Forall {
        /// Binder name (or `_`).
        var: String,
        /// Binder sort identifier.
        sort: String,
        /// Body expression (uses the binder).
        body: Box<IRExpr>,
    },

    /// ∃ var:sort, body.
    #[serde(rename = "exists")]
    Exists {
        /// Binder name (or `_`).
        var: String,
        /// Binder sort identifier.
        sort: String,
        /// Body expression.
        body: Box<IRExpr>,
    },

    /// Conjunction.
    #[serde(rename = "and")]
    And {
        /// Left conjunct.
        left: Box<IRExpr>,
        /// Right conjunct.
        right: Box<IRExpr>,
    },

    /// Disjunction.
    #[serde(rename = "or")]
    Or {
        /// Left disjunct.
        left: Box<IRExpr>,
        /// Right disjunct.
        right: Box<IRExpr>,
    },

    /// Negation.
    #[serde(rename = "not")]
    Not {
        /// Body of the negation.
        body: Box<IRExpr>,
    },

    /// Material implication `left → right`.
    #[serde(rename = "implies")]
    Implies {
        /// Antecedent.
        left: Box<IRExpr>,
        /// Consequent.
        right: Box<IRExpr>,
    },

    /// Biconditional `left ↔ right`.
    #[serde(rename = "iff")]
    Iff {
        /// Left side.
        left: Box<IRExpr>,
        /// Right side.
        right: Box<IRExpr>,
    },

    /// Term-level equality `left = right`.
    #[serde(rename = "eq")]
    Eq {
        /// LHS term.
        left: Box<IRExpr>,
        /// RHS term.
        right: Box<IRExpr>,
    },

    /// Term-level disequality `left ≠ right`.
    #[serde(rename = "neq")]
    Neq {
        /// LHS term.
        left: Box<IRExpr>,
        /// RHS term.
        right: Box<IRExpr>,
    },

    /// `left ≤ right`.
    #[serde(rename = "leq")]
    Leq {
        /// LHS.
        left: Box<IRExpr>,
        /// RHS.
        right: Box<IRExpr>,
    },

    /// `left < right`.
    #[serde(rename = "lt")]
    Lt {
        /// LHS.
        left: Box<IRExpr>,
        /// RHS.
        right: Box<IRExpr>,
    },

    /// `element ∈ collection`.
    #[serde(rename = "mem")]
    Mem {
        /// The element being tested.
        element: Box<IRExpr>,
        /// The collection it's tested against.
        collection: Box<IRExpr>,
    },

    /// Natural-number literal.
    #[serde(rename = "nat_lit")]
    NatLit {
        /// The literal value.
        value: u64,
    },

    /// Propositional ⊤.
    #[serde(rename = "true")]
    True,

    /// Propositional ⊥.
    #[serde(rename = "false")]
    False,

    /// A construct Phase A couldn't translate.  Description carries the
    /// reason; the Phase B translator skips axioms containing these.
    #[serde(rename = "unsupported")]
    Unsupported {
        /// Human-readable description from the exporter.
        description: String,
    },
}

impl LeanIR {
    /// Run a cheap structural validation pass.
    ///
    /// Returns a list of human-readable warnings for issues that don't prevent
    /// translation but are worth surfacing: dangling sort references in
    /// constructors / functions / predicates, and duplicate top-level names.
    pub fn validate(&self) -> Vec<String> {
        use std::collections::BTreeSet;

        let mut warnings = Vec::new();
        let known_sorts: BTreeSet<&str> = self
            .sorts
            .iter()
            .map(|s| s.name.as_str())
            .chain(BUILTIN_SORTS.iter().copied())
            .collect();

        for c in &self.constructors {
            if !known_sorts.contains(c.sort.as_str()) {
                warnings.push(format!(
                    "constructor '{}' references unknown sort '{}'",
                    c.name, c.sort
                ));
            }
            for field in &c.fields {
                if !known_sorts.contains(field.as_str()) && !is_placeholder_sort(field) {
                    // Field sorts referencing unseen sorts are surfaced but
                    // not treated as errors — Pass 1 of the translator
                    // synthesises them from context.
                    warnings.push(format!(
                        "constructor '{}' field references unknown sort '{}'",
                        c.name, field
                    ));
                }
            }
        }

        for f in &self.functions {
            for s in &f.domain {
                if !known_sorts.contains(s.as_str()) && !is_placeholder_sort(s) {
                    warnings.push(format!(
                        "function '{}' domain references unknown sort '{}'",
                        f.name, s
                    ));
                }
            }
            if !known_sorts.contains(f.codomain.as_str()) && !is_placeholder_sort(&f.codomain) {
                warnings.push(format!(
                    "function '{}' codomain references unknown sort '{}'",
                    f.name, f.codomain
                ));
            }
        }

        for p in &self.predicates {
            for param in &p.params {
                if !known_sorts.contains(param.sort.as_str())
                    && !is_placeholder_sort(&param.sort)
                {
                    warnings.push(format!(
                        "predicate '{}' parameter '{}' references unknown sort '{}'",
                        p.name, param.name, param.sort
                    ));
                }
            }
        }

        // Duplicate name check across the top-level symbol kinds.
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        let names = self
            .sorts
            .iter()
            .map(|s| s.name.as_str())
            .chain(self.constructors.iter().map(|c| c.name.as_str()))
            .chain(self.functions.iter().map(|f| f.name.as_str()))
            .chain(self.predicates.iter().map(|p| p.name.as_str()));
        for n in names {
            if !seen.insert(n) {
                warnings.push(format!("duplicate top-level name: '{n}'"));
            }
        }

        warnings
    }
}

/// Sort identifiers that are always considered known even when not declared in
/// `ir.sorts`.  These match Phase A's exporter conventions plus the Lean
/// stdlib types that flow through built-in operations.
pub const BUILTIN_SORTS: &[&str] = &["Nat", "Int", "Bool", "Prop"];

/// True for sort identifiers the translator synthesises lazily and which
/// `validate` should therefore ignore:
///
///   * Placeholders the exporter emits when it can't resolve a binder type
///     (`_Param`, `_Sort`, `_Unknown` …).
///   * Mangled parameterized types like `List_Nat`, `Repr_Tree`, `Std_Format`
///     — Phase A flattens `List Nat` to `List_Nat`; these aren't declared in
///     `ir.sorts` but Pass 1 picks them up from usage.
fn is_placeholder_sort(s: &str) -> bool {
    s.starts_with('_') || s.contains('_')
}

#[cfg(test)]
mod tests {
    use super::*;

    fn load(name: &str) -> LeanIR {
        let path = format!("tests/fixtures/{name}.ir.json");
        let contents = std::fs::read_to_string(&path)
            .unwrap_or_else(|_| panic!("missing fixture {path}; run the Phase A regeneration script"));
        serde_json::from_str(&contents).expect("fixture must deserialize")
    }

    #[test]
    fn test_deserialize_minimal() {
        let ir = load("minimal");
        assert_eq!(ir.sorts.len(), 0);
        assert_eq!(ir.predicates.len(), 2);
        assert_eq!(ir.theorems.len(), 2);
        let names: Vec<&str> = ir.predicates.iter().map(|p| p.name.as_str()).collect();
        assert!(names.contains(&"Even"));
        assert!(names.contains(&"Pos"));
    }

    #[test]
    fn test_deserialize_bst() {
        let ir = load("bst");
        assert_eq!(ir.sorts.len(), 1);
        assert_eq!(ir.sorts[0].name, "Tree");
        assert_eq!(ir.constructors.len(), 2);
        assert_eq!(ir.predicates.len(), 1);
        let sorted = ir.predicates.iter().find(|p| p.name == "Sorted").expect("Sorted predicate");
        assert_eq!(sorted.equations.len(), 3, "Sorted should have three equation lemmas");
        assert_eq!(ir.theorems.len(), 3);
    }

    #[test]
    fn test_deserialize_hypotheses() {
        let ir = load("hypotheses");
        assert_eq!(ir.theorems.len(), 3);
        let counts: Vec<usize> = ir.theorems.iter().map(|t| t.hypotheses.len()).collect();
        // Order is environment-dependent; assert as a multiset.
        let mut sorted_counts = counts.clone();
        sorted_counts.sort_unstable();
        assert_eq!(sorted_counts, vec![1, 2, 2]);
    }

    #[test]
    fn test_deserialize_sort_lean() {
        let ir = load("sort_lean");
        assert_eq!(ir.predicates.len(), 4);
        assert_eq!(ir.theorems.len(), 3);
        assert_eq!(ir.warnings.len(), 10);
    }

    #[test]
    fn test_deserialize_empty() {
        let s = r#"{"sorts":[],"constructors":[],"functions":[],"predicates":[],"theorems":[]}"#;
        let ir: LeanIR = serde_json::from_str(s).expect("empty IR deserializes");
        assert!(ir.sorts.is_empty());
        assert!(ir.predicates.is_empty());
        assert!(ir.theorems.is_empty());
    }

    #[test]
    fn test_nat_lit_round_trip() {
        let s = r#"{"kind":"nat_lit","value":42}"#;
        let e: IRExpr = serde_json::from_str(s).expect("nat_lit");
        match e {
            IRExpr::NatLit { value } => assert_eq!(value, 42),
            other => panic!("expected NatLit, got {other:?}"),
        }
    }

    #[test]
    fn test_hypothesis_named_form() {
        let s = r#"{"name":"h","body":{"kind":"true"}}"#;
        let h: IRHypothesis = serde_json::from_str(s).expect("named hyp");
        assert!(matches!(h.body(), IRExpr::True));
        match h {
            IRHypothesis::Named { name, .. } => assert_eq!(name, "h"),
            _ => panic!("expected Named form"),
        }
    }

    #[test]
    fn test_validate_good() {
        let ir = load("bst");
        let warnings = ir.validate();
        assert!(
            warnings.is_empty(),
            "expected no validation warnings on bst, got: {warnings:?}"
        );
    }

    #[test]
    fn test_validate_dangling_sort() {
        let ir = LeanIR {
            version: Some(1),
            source_file: None,
            sorts: vec![IRSort {
                name: "A".into(),
                kind: "inductive".into(),
                num_params: Some(0),
                num_ctors: Some(1),
            }],
            constructors: vec![IRConstructor {
                name: "A.mk".into(),
                sort: "B".into(), // dangling
                fields: vec![],
            }],
            functions: vec![],
            predicates: vec![],
            theorems: vec![],
            warnings: vec![],
        };
        let w = ir.validate();
        assert!(
            w.iter().any(|s| s.contains("unknown sort 'B'")),
            "expected dangling-sort warning, got: {w:?}"
        );
    }

    #[test]
    fn test_validate_duplicate_name() {
        let ir = LeanIR {
            version: Some(1),
            source_file: None,
            sorts: vec![IRSort {
                name: "X".into(),
                kind: "inductive".into(),
                num_params: Some(0),
                num_ctors: Some(0),
            }],
            constructors: vec![],
            functions: vec![IRFunction {
                name: "X".into(), // collides with sort
                domain: vec![],
                codomain: "Nat".into(),
                equations: vec![],
            }],
            predicates: vec![],
            theorems: vec![],
            warnings: vec![],
        };
        let w = ir.validate();
        assert!(
            w.iter().any(|s| s.contains("duplicate top-level name")),
            "expected duplicate-name warning, got: {w:?}"
        );
    }
}
