//! Integration tests for `specmut-lean` translator.
//!
//! Every test reads a pre-generated JSON fixture from `tests/fixtures/`.
//! The `lean` toolchain is not required at test time — Phase A produces the
//! fixtures via `lean --run specmut_export.lean <target.lean>`.

use specmut_core::formula::{Formula, Term};
use specmut_core::signature::{FunctionSymbol, RelationSymbol, Signature, SortSymbol};
use specmut_lean::ir_types::{
    IREquation, IRExpr, IRFunction, IRHypothesis, IRParam, IRPredicate, IRSort, IRTheorem, LeanIR,
};
use specmut_lean::translator::{
    deduplicate_axioms, filter_signature, LeanTranslator, TranslationError, TranslationResult,
};

fn load_fixture(name: &str) -> LeanIR {
    let path = format!("tests/fixtures/{name}.ir.json");
    let contents = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("missing fixture {path}: {e}"));
    serde_json::from_str(&contents).expect("fixture deserializes")
}

fn run(name: &str) -> TranslationResult {
    let ir = load_fixture(name);
    LeanTranslator::translate(&ir).unwrap_or_else(|e| panic!("translate({name}) failed: {e}"))
}

// ----------------------------------------------------------------------------
// End-to-end per-fixture
// ----------------------------------------------------------------------------

#[test]
fn test_e2e_minimal() {
    let r = run("minimal");
    assert!(!r.axioms.is_empty(), "should produce axioms");
    assert!(r.signature.sorts.iter().any(|s| s.name == "Nat"));
    for axiom in &r.axioms {
        assert!(axiom.is_sentence(), "axiom not a sentence: {axiom:?}");
        assert!(is_nnf(axiom), "axiom not in NNF: {axiom:?}");
    }
}

#[test]
fn test_e2e_bst() {
    let r = run("bst");
    // Sorted contributes 3 equations; theorems contribute 3.  Functions
    // (Tree.contains etc.) contribute more from their equation lemmas.
    assert!(
        r.signature.sorts.iter().any(|s| s.name == "Tree"),
        "Tree sort missing: {:?}",
        r.signature.sorts
    );
    assert!(
        r.signature.functions.iter().any(|f| f.name == "Tree.leaf"),
        "Tree.leaf function missing"
    );
    assert!(
        r.signature.functions.iter().any(|f| f.name == "Tree.node"),
        "Tree.node function missing"
    );
    assert!(
        r.signature.relations.iter().any(|rel| rel.name == "Sorted"),
        "Sorted relation missing"
    );
    assert_eq!(
        r.translated_theorems.len(),
        3,
        "all three BST theorems should translate"
    );
    // Should have at least Sorted's 3 equations + 3 theorems = 6 axioms (more if
    // Tree.contains / instReprTree.repr equations succeed).
    assert!(
        r.axioms.len() >= 6,
        "expected ≥6 axioms, got {}",
        r.axioms.len()
    );
    for axiom in &r.axioms {
        assert!(axiom.is_sentence(), "non-sentence: {axiom:?}");
        assert!(is_nnf(axiom), "non-NNF: {axiom:?}");
    }
}

#[test]
fn test_e2e_hypotheses() {
    let r = run("hypotheses");
    assert_eq!(r.translated_theorems.len(), 3);
    assert!(r.axioms.len() >= 3);
}

#[test]
fn test_e2e_sort_lean() {
    let r = run("sort_lean");
    assert!(
        r.translated_predicates.len() + r.translated_theorems.len() >= 2,
        "at least two declarations should translate from sort_lean.ir.json"
    );
}

// ----------------------------------------------------------------------------
// Sort resolution
// ----------------------------------------------------------------------------

#[test]
fn test_builtin_sorts_kept_when_referenced() {
    // Phase D: sort filtering drops sorts no axiom mentions.  Minimal.lean's
    // axioms reference `Nat` (via the predicates' parameter sort) but not
    // `Bool`/`Int`/`Prop`, so only `Nat` survives.  Confirm `Nat` is kept and
    // an unreferenced built-in like `Bool` is filtered.
    let r = run("minimal");
    assert!(
        r.signature.sorts.iter().any(|s| s.name == "Nat"),
        "Nat should survive filtering: {:?}",
        r.signature.sorts
    );
    assert!(
        !r.signature.sorts.iter().any(|s| s.name == "Bool"),
        "Bool should be filtered out: {:?}",
        r.signature.sorts
    );
}

#[test]
fn test_inductive_sort_in_signature() {
    let r = run("bst");
    assert!(r.signature.sorts.iter().any(|s| s.name == "Tree"));
}

#[test]
fn test_parameterized_sort_mangling_preserved() {
    let r = run("bst");
    // List_Nat is referenced by Sorted's param.
    assert!(
        r.signature.sorts.iter().any(|s| s.name == "List_Nat"),
        "expected List_Nat sort, got {:?}",
        r.signature.sorts
    );
}

// ----------------------------------------------------------------------------
// Constructor → function symbol
// ----------------------------------------------------------------------------

#[test]
fn test_constructor_as_function_leaf() {
    let r = run("bst");
    let leaf = r
        .signature
        .functions
        .iter()
        .find(|f| f.name == "Tree.leaf")
        .expect("Tree.leaf in signature");
    assert!(leaf.domain.is_empty(), "Tree.leaf is a constant");
    assert_eq!(leaf.codomain.name, "Tree");
}

#[test]
fn test_constructor_as_function_node() {
    let r = run("bst");
    let node = r
        .signature
        .functions
        .iter()
        .find(|f| f.name == "Tree.node")
        .expect("Tree.node in signature");
    assert_eq!(node.domain.len(), 3);
    assert_eq!(node.codomain.name, "Tree");
    // Tree → Nat → Tree → Tree (per Phase A fixture).
    assert_eq!(node.domain[0].name, "Tree");
    assert_eq!(node.domain[1].name, "Nat");
    assert_eq!(node.domain[2].name, "Tree");
}

// ----------------------------------------------------------------------------
// Predicate equations
// ----------------------------------------------------------------------------

#[test]
fn test_sorted_equations_translate() {
    let r = run("bst");
    assert!(
        r.translated_predicates.contains(&"Sorted".to_string()),
        "Sorted should be among translated_predicates"
    );
    // Each equation becomes one axiom; 3 equations → at least 3 axioms from Sorted alone.
    // We check this indirectly: there must be at least 3 sentences mentioning Sorted's relation.
    let sorted_axioms: usize = r
        .axioms
        .iter()
        .filter(|a| formula_references_relation(a, "Sorted"))
        .count();
    assert!(
        sorted_axioms >= 3,
        "expected ≥3 axioms referencing Sorted, got {sorted_axioms}"
    );
}

#[test]
fn test_even_equation_translates() {
    let r = run("minimal");
    assert!(r.translated_predicates.contains(&"Even".to_string()));
}

// ----------------------------------------------------------------------------
// Theorem translation
// ----------------------------------------------------------------------------

#[test]
fn test_theorem_no_hypotheses_minimal() {
    let r = run("minimal");
    assert_eq!(r.translated_theorems.len(), 2);
}

#[test]
fn test_theorem_with_hypotheses_count() {
    let ir = load_fixture("hypotheses");
    let mut counts: Vec<usize> = ir.theorems.iter().map(|t| t.hypotheses.len()).collect();
    counts.sort_unstable();
    assert_eq!(counts, vec![1, 2, 2]);
}

#[test]
fn test_theorem_with_two_hypotheses_translates() {
    let r = run("hypotheses");
    // All three theorems should make it through.
    assert_eq!(
        r.translated_theorems.len(),
        3,
        "skipped: {:?}",
        r.skipped_theorems
    );
}

// ----------------------------------------------------------------------------
// Expression translation
// ----------------------------------------------------------------------------

#[test]
fn test_forall_debruijn_single() {
    // ∀ x:Nat, x = x
    let body = IRExpr::Eq {
        left: Box::new(IRExpr::Var { name: "x".into() }),
        right: Box::new(IRExpr::Var { name: "x".into() }),
    };
    let ir = make_thm_ir(
        "refl_x",
        IRExpr::Forall {
            var: "x".into(),
            sort: "Nat".into(),
            body: Box::new(body),
        },
    );
    let r = LeanTranslator::translate(&ir).expect("ok");
    assert_eq!(r.axioms.len(), 1);
    let nat = SortSymbol::new("Nat");
    let expected = Formula::Forall {
        sort: nat,
        body: Box::new(Formula::Eq(Term::Var(0), Term::Var(0))),
    };
    assert_eq!(r.axioms[0], expected);
}

#[test]
fn test_nested_forall_debruijn() {
    // ∀ x:Nat, ∀ y:Nat, R x y — but R isn't a known predicate, so we use an
    // equality to keep this within scope of declared symbols.
    // ∀ x:Nat, ∀ y:Nat, x = y
    let inner = IRExpr::Eq {
        left: Box::new(IRExpr::Var { name: "x".into() }),
        right: Box::new(IRExpr::Var { name: "y".into() }),
    };
    let body = IRExpr::Forall {
        var: "y".into(),
        sort: "Nat".into(),
        body: Box::new(inner),
    };
    let outer = IRExpr::Forall {
        var: "x".into(),
        sort: "Nat".into(),
        body: Box::new(body),
    };
    let ir = make_thm_ir("eq_xy", outer);
    let r = LeanTranslator::translate(&ir).expect("ok");
    assert_eq!(r.axioms.len(), 1);
    // Outer binds x → de Bruijn 1 inside the inner ∀; y → de Bruijn 0.
    let nat = SortSymbol::new("Nat");
    let expected = Formula::Forall {
        sort: nat.clone(),
        body: Box::new(Formula::Forall {
            sort: nat,
            body: Box::new(Formula::Eq(Term::Var(1), Term::Var(0))),
        }),
    };
    assert_eq!(r.axioms[0], expected);
}

#[test]
fn test_implies_desugar() {
    // True → False  becomes (¬⊤ ∨ ⊥) which to_nnf collapses to (⊥ ∨ ⊥).
    let ir = make_thm_ir(
        "t",
        IRExpr::Implies {
            left: Box::new(IRExpr::True),
            right: Box::new(IRExpr::False),
        },
    );
    let r = LeanTranslator::translate(&ir).expect("ok");
    assert_eq!(r.axioms.len(), 1);
    let axiom = &r.axioms[0];
    assert!(is_nnf(axiom), "implies output not NNF: {axiom:?}");
    // It should be Or with ⊥ in both positions after NNF.
    let expected = Formula::Or(Box::new(Formula::Bot), Box::new(Formula::Bot));
    assert_eq!(axiom, &expected);
}

#[test]
fn test_iff_desugar() {
    // True ↔ True  →  (⊤ → ⊤) ∧ (⊤ → ⊤)  →  (⊥ ∨ ⊤) ∧ (⊥ ∨ ⊤)  (in NNF)
    let ir = make_thm_ir(
        "t",
        IRExpr::Iff {
            left: Box::new(IRExpr::True),
            right: Box::new(IRExpr::True),
        },
    );
    let r = LeanTranslator::translate(&ir).expect("ok");
    let axiom = &r.axioms[0];
    assert!(is_nnf(axiom));
    assert!(matches!(axiom, Formula::And(_, _)));
}

#[test]
fn test_leq_auto_declares_relation() {
    let ir = make_thm_ir(
        "le_self",
        IRExpr::Forall {
            var: "n".into(),
            sort: "Nat".into(),
            body: Box::new(IRExpr::Leq {
                left: Box::new(IRExpr::Var { name: "n".into() }),
                right: Box::new(IRExpr::Var { name: "n".into() }),
            }),
        },
    );
    let r = LeanTranslator::translate(&ir).expect("ok");
    assert!(
        r.signature.relations.iter().any(|rel| rel.name == "leq"),
        "leq should be auto-declared, got {:?}",
        r.signature.relations
    );
}

#[test]
fn test_lt_auto_declares_relation() {
    let ir = make_thm_ir(
        "lt",
        IRExpr::Forall {
            var: "n".into(),
            sort: "Nat".into(),
            body: Box::new(IRExpr::Lt {
                left: Box::new(IRExpr::Var { name: "n".into() }),
                right: Box::new(IRExpr::Var { name: "n".into() }),
            }),
        },
    );
    let r = LeanTranslator::translate(&ir).expect("ok");
    assert!(r.signature.relations.iter().any(|rel| rel.name == "lt"));
}

#[test]
fn test_nat_lit_translation() {
    // ∀ n:Nat, n = 3  → succ-chain expansion of 3
    let ir = make_thm_ir(
        "eq_three",
        IRExpr::Forall {
            var: "n".into(),
            sort: "Nat".into(),
            body: Box::new(IRExpr::Eq {
                left: Box::new(IRExpr::Var { name: "n".into() }),
                right: Box::new(IRExpr::NatLit { value: 3 }),
            }),
        },
    );
    let r = LeanTranslator::translate(&ir).expect("ok");
    assert!(r.signature.functions.iter().any(|f| f.name == "zero"));
    assert!(r.signature.functions.iter().any(|f| f.name == "succ"));
    // Drill into the axiom and confirm depth-3 succ chain on the RHS.
    if let Formula::Forall { body, .. } = &r.axioms[0] {
        if let Formula::Eq(_, rhs) = body.as_ref() {
            assert_eq!(succ_chain_depth(rhs), 3);
            return;
        }
    }
    panic!("axiom shape unexpected: {:?}", r.axioms[0]);
}

#[test]
fn test_app_arithmetic_auto_declares() {
    // ∀ n:Nat, n + n = n  → auto-declare `add`
    let ir = make_thm_ir(
        "add",
        IRExpr::Forall {
            var: "n".into(),
            sort: "Nat".into(),
            body: Box::new(IRExpr::Eq {
                left: Box::new(IRExpr::App {
                    fn_name: "add".into(),
                    args: vec![
                        IRExpr::Var { name: "n".into() },
                        IRExpr::Var { name: "n".into() },
                    ],
                }),
                right: Box::new(IRExpr::Var { name: "n".into() }),
            }),
        },
    );
    let r = LeanTranslator::translate(&ir).expect("ok");
    let add = r
        .signature
        .functions
        .iter()
        .find(|f| f.name == "add")
        .expect("add auto-declared");
    assert_eq!(add.domain.len(), 2);
    assert_eq!(add.domain[0].name, "Nat");
    assert_eq!(add.domain[1].name, "Nat");
}

// ----------------------------------------------------------------------------
// Unsupported handling
// ----------------------------------------------------------------------------

#[test]
fn test_unsupported_in_one_theorem_skips_gracefully() {
    // Build an IR with one good theorem and one Unsupported one.
    let mut ir = make_thm_ir("good", IRExpr::True);
    ir.theorems.push(IRTheorem {
        name: "bad".into(),
        hypotheses: vec![],
        conclusion: IRExpr::Unsupported {
            description: "test".into(),
        },
    });
    let r = LeanTranslator::translate(&ir).expect("partial ok");
    assert_eq!(r.translated_theorems, vec!["good".to_string()]);
    assert_eq!(r.skipped_theorems.len(), 1);
    assert_eq!(r.skipped_theorems[0].0, "bad");
}

#[test]
fn test_all_unsupported_is_nothing_translatable() {
    let ir = LeanIR {
        version: Some(1),
        source_file: None,
        sorts: vec![],
        constructors: vec![],
        functions: vec![],
        predicates: vec![],
        theorems: vec![IRTheorem {
            name: "bad".into(),
            hypotheses: vec![],
            conclusion: IRExpr::Unsupported {
                description: "no".into(),
            },
        }],
        warnings: vec![],
    };
    let err = LeanTranslator::translate(&ir).expect_err("should fail");
    assert!(matches!(err, TranslationError::NothingTranslatable { .. }));
}

#[test]
fn test_recursive_predicate_body_is_unsupported_but_equations_save_it() {
    // Build a predicate with both unsupported body AND equations.  The
    // equations should drive translation; body fallback shouldn't fire.
    let nat_sort = "Nat";
    let pred = IRPredicate {
        name: "P".into(),
        params: vec![IRParam {
            name: "n".into(),
            sort: nat_sort.into(),
        }],
        body: IRExpr::Unsupported {
            description: "recursive".into(),
        },
        equations: vec![IREquation {
            vars: vec![],
            lhs: IRExpr::App {
                fn_name: "P".into(),
                args: vec![IRExpr::NatLit { value: 0 }],
            },
            rhs: IRExpr::True,
        }],
    };
    let ir = LeanIR {
        version: Some(1),
        source_file: None,
        sorts: vec![],
        constructors: vec![],
        functions: vec![],
        predicates: vec![pred],
        theorems: vec![],
        warnings: vec![],
    };
    let r = LeanTranslator::translate(&ir).expect("ok");
    assert_eq!(r.translated_predicates, vec!["P".to_string()]);
    assert_eq!(r.axioms.len(), 1, "equation → one axiom");
}

#[test]
fn test_skipped_does_not_panic_on_sort_lean() {
    // sort_lean.ir.json has 10 elaboration-error warnings.  Make sure we
    // still translate the parts that work and don't panic.
    let r = run("sort_lean");
    // Warnings are inherited from the IR plus any added during translation.
    assert!(r.warnings.len() >= 10);
}

// ----------------------------------------------------------------------------
// Empty IR
// ----------------------------------------------------------------------------

#[test]
fn test_empty_ir_is_nothing_translatable() {
    let ir = LeanIR {
        version: Some(1),
        source_file: None,
        sorts: vec![],
        constructors: vec![],
        functions: vec![],
        predicates: vec![],
        theorems: vec![],
        warnings: vec![],
    };
    let err = LeanTranslator::translate(&ir).expect_err("empty IR has no axioms");
    assert!(matches!(err, TranslationError::NothingTranslatable { .. }));
}

// ----------------------------------------------------------------------------
// Invariant checks
// ----------------------------------------------------------------------------

#[test]
fn test_signature_constructible_across_fixtures() {
    for name in ["minimal", "bst", "hypotheses", "sort_lean"] {
        let r = run(name);
        // If translate() returns Ok, Signature::new succeeded.  Re-validate
        // by reconstructing from the parts.
        let sorts: Vec<_> = r.signature.sorts.iter().cloned().collect();
        let fns: Vec<_> = r.signature.functions.iter().cloned().collect();
        let rels: Vec<_> = r.signature.relations.iter().cloned().collect();
        Signature::new(sorts, fns, rels).expect(name);
    }
}

#[test]
fn test_all_axioms_are_sentences_across_fixtures() {
    for name in ["minimal", "bst", "hypotheses"] {
        let r = run(name);
        for (i, a) in r.axioms.iter().enumerate() {
            assert!(
                a.is_sentence(),
                "fixture {name} axiom {i} not a sentence: {a:?}"
            );
        }
    }
}

#[test]
fn test_all_axioms_are_nnf_across_fixtures() {
    for name in ["minimal", "bst", "hypotheses"] {
        let r = run(name);
        for (i, a) in r.axioms.iter().enumerate() {
            assert!(is_nnf(a), "fixture {name} axiom {i} not NNF: {a:?}");
        }
    }
}

// ----------------------------------------------------------------------------
// Edge case hardening (Phase D §7)
// ----------------------------------------------------------------------------

#[test]
fn test_sort_name_collision_renames_relation() {
    // Inductive named `leq` — collides with the auto-declared `leq` relation
    // when a theorem uses `≤`.  The translator should rename the relation
    // rather than crash with a duplicate-name signature error.
    let ir = LeanIR {
        version: Some(1),
        source_file: None,
        sorts: vec![IRSort {
            name: "leq".into(),
            kind: "inductive".into(),
            num_params: Some(0),
            num_ctors: Some(0),
        }],
        constructors: vec![],
        functions: vec![],
        predicates: vec![],
        theorems: vec![IRTheorem {
            name: "t".into(),
            hypotheses: vec![],
            conclusion: IRExpr::Forall {
                var: "n".into(),
                sort: "Nat".into(),
                body: Box::new(IRExpr::Leq {
                    left: Box::new(IRExpr::Var { name: "n".into() }),
                    right: Box::new(IRExpr::Var { name: "n".into() }),
                }),
            },
        }],
        warnings: vec![],
    };
    let r = LeanTranslator::translate(&ir).expect("ok despite collision");
    // The auto-declared relation must have been renamed.
    assert!(
        r.signature.relations.iter().any(|rel| rel.name.contains("auto") && rel.name.contains("leq")),
        "expected renamed leq relation, got {:?}",
        r.signature.relations
    );
}

#[test]
fn test_large_axiom_count_warning() {
    // Predicate with 25 equations → translator emits a "large axiom set" warning.
    let nat = "Nat";
    let equations: Vec<IREquation> = (0..25)
        .map(|_| IREquation {
            vars: vec![],
            lhs: IRExpr::App {
                fn_name: "P".into(),
                args: vec![IRExpr::NatLit { value: 0 }],
            },
            rhs: IRExpr::True,
        })
        .collect();
    let ir = LeanIR {
        version: Some(1),
        source_file: None,
        sorts: vec![],
        constructors: vec![],
        functions: vec![],
        predicates: vec![IRPredicate {
            name: "P".into(),
            params: vec![IRParam {
                name: "n".into(),
                sort: nat.into(),
            }],
            body: IRExpr::True,
            equations,
        }],
        theorems: vec![],
        warnings: vec![],
    };
    let r = LeanTranslator::translate(&ir).expect("ok");
    // After dedup the 25 identical equations collapse to one, so this
    // configuration *should not* trigger the large-axiom warning.
    assert_eq!(r.axioms.len(), 1, "dedup should collapse identical axioms");
    assert!(
        !r.warnings.iter().any(|w| w.contains("large axiom set")),
        "dedup-collapsed set shouldn't warn: {:?}",
        r.warnings
    );
}

#[test]
fn test_dedup_then_large_warning_with_distinct_axioms() {
    // 25 *distinct* axioms — dedup keeps them all, warning fires.
    let nat = "Nat";
    let equations: Vec<IREquation> = (0..25)
        .map(|i| IREquation {
            vars: vec![],
            lhs: IRExpr::App {
                fn_name: "P".into(),
                args: vec![IRExpr::NatLit { value: i as u64 }],
            },
            rhs: IRExpr::True,
        })
        .collect();
    let ir = LeanIR {
        version: Some(1),
        source_file: None,
        sorts: vec![],
        constructors: vec![],
        functions: vec![],
        predicates: vec![IRPredicate {
            name: "P".into(),
            params: vec![IRParam {
                name: "n".into(),
                sort: nat.into(),
            }],
            body: IRExpr::True,
            equations,
        }],
        theorems: vec![],
        warnings: vec![],
    };
    let r = LeanTranslator::translate(&ir).expect("ok");
    assert_eq!(r.axioms.len(), 25);
    assert!(
        r.warnings.iter().any(|w| w.contains("large axiom set")),
        "expected large-axiom warning: {:?}",
        r.warnings
    );
}

#[test]
fn test_nat_lit_overflow_does_not_panic() {
    // NatLit(5) on a model bound that only has elements {0,1}.
    let ir = LeanIR {
        version: Some(1),
        source_file: None,
        sorts: vec![],
        constructors: vec![],
        functions: vec![],
        predicates: vec![],
        theorems: vec![IRTheorem {
            name: "t".into(),
            hypotheses: vec![],
            conclusion: IRExpr::Forall {
                var: "n".into(),
                sort: "Nat".into(),
                body: Box::new(IRExpr::Eq {
                    left: Box::new(IRExpr::Var { name: "n".into() }),
                    right: Box::new(IRExpr::NatLit { value: 5 }),
                }),
            },
        }],
        warnings: vec![],
    };
    let r = LeanTranslator::translate(&ir).expect("ok");
    // Translation itself should succeed; the succ-chain has depth 5 but the
    // formula is structurally valid.
    assert_eq!(r.axioms.len(), 1);
    assert!(r.axioms[0].is_sentence());
}

// ----------------------------------------------------------------------------
// Sort filtering (Phase D)
// ----------------------------------------------------------------------------

#[test]
fn test_filter_removes_unreferenced_sorts() {
    let nat = SortSymbol::new("Nat");
    let tree = SortSymbol::new("Tree");
    let std_format = SortSymbol::new("Std_Format");
    let bool_s = SortSymbol::new("Bool");
    let sig = Signature::new(
        vec![nat.clone(), tree.clone(), std_format.clone(), bool_s.clone()],
        vec![],
        vec![RelationSymbol::new("Sorted", vec![tree.clone()])],
    )
    .expect("sig");
    // Axiom references Tree only.
    let axiom = Formula::Forall {
        sort: tree.clone(),
        body: Box::new(Formula::Atom {
            relation: RelationSymbol::new("Sorted", vec![tree.clone()]),
            args: vec![Term::Var(0)],
        }),
    };
    let filtered = filter_signature(&sig, &[axiom]).expect("filter");
    assert!(filtered.sorts.iter().any(|s| s.name == "Tree"));
    assert!(!filtered.sorts.iter().any(|s| s.name == "Std_Format"));
    assert!(!filtered.sorts.iter().any(|s| s.name == "Bool"));
    assert!(!filtered.sorts.iter().any(|s| s.name == "Nat"));
}

#[test]
fn test_filter_transitive_closure_through_function() {
    // Tree is referenced; Tree.node : Tree×Nat×Tree → Tree pulls Nat in too.
    let nat = SortSymbol::new("Nat");
    let tree = SortSymbol::new("Tree");
    let prop = SortSymbol::new("Prop");
    let node = FunctionSymbol::new(
        "node",
        vec![tree.clone(), nat.clone(), tree.clone()],
        tree.clone(),
    );
    let sig = Signature::new(
        vec![nat.clone(), tree.clone(), prop.clone()],
        vec![node],
        vec![RelationSymbol::new("Sorted", vec![tree.clone()])],
    )
    .expect("sig");
    let axiom = Formula::Forall {
        sort: tree.clone(),
        body: Box::new(Formula::Atom {
            relation: RelationSymbol::new("Sorted", vec![tree.clone()]),
            args: vec![Term::Var(0)],
        }),
    };
    let filtered = filter_signature(&sig, &[axiom]).expect("filter");
    let names: Vec<&str> = filtered.sorts.iter().map(|s| s.name.as_str()).collect();
    assert!(names.contains(&"Tree"), "Tree missing: {names:?}");
    assert!(names.contains(&"Nat"), "Nat should be reachable via node: {names:?}");
    assert!(!names.contains(&"Prop"), "Prop should be filtered: {names:?}");
}

#[test]
fn test_filter_keeps_all_when_all_referenced() {
    let nat = SortSymbol::new("Nat");
    let sig = Signature::new(
        vec![nat.clone()],
        vec![],
        vec![RelationSymbol::new("P", vec![nat.clone()])],
    )
    .expect("sig");
    let axiom = Formula::Forall {
        sort: nat.clone(),
        body: Box::new(Formula::Atom {
            relation: RelationSymbol::new("P", vec![nat.clone()]),
            args: vec![Term::Var(0)],
        }),
    };
    let filtered = filter_signature(&sig, &[axiom]).expect("filter");
    assert_eq!(filtered.sorts.len(), 1);
}

#[test]
fn test_filter_bst_fixture_drops_noise() {
    let r = run("bst");
    let kept: Vec<&str> = r.signature.sorts.iter().map(|s| s.name.as_str()).collect();
    // Tree is the spec's domain — must survive.
    assert!(kept.contains(&"Tree"), "Tree missing: {kept:?}");
    // Std_Format is stdlib pretty-printing noise — must NOT survive.
    // (Post Phase G it's filtered at the exporter level so it never
    // reaches the sort filter; assertion still holds.)
    assert!(
        !kept.contains(&"Std_Format"),
        "Std_Format should be filtered out: {kept:?}"
    );
    // Phase G additional invariant: no `inst*` / `Repr*` sorts leak
    // through.
    for k in &kept {
        assert!(
            !k.contains("Repr") && !k.starts_with("inst"),
            "noise sort '{k}' should be suppressed"
        );
    }
}

// ----------------------------------------------------------------------------
// Deduplication
// ----------------------------------------------------------------------------

#[test]
fn test_deduplicate_removes_identical() {
    let a = Formula::Top;
    let dup = vec![a.clone(), a.clone(), Formula::Bot];
    let result = deduplicate_axioms(dup);
    assert_eq!(result.len(), 2);
    assert!(result.contains(&Formula::Top));
    assert!(result.contains(&Formula::Bot));
}

#[test]
fn test_deduplicate_preserves_distinct() {
    let nat = SortSymbol::new("Nat");
    let f1 = Formula::Forall {
        sort: nat.clone(),
        body: Box::new(Formula::Top),
    };
    let f2 = Formula::Exists {
        sort: nat,
        body: Box::new(Formula::Top),
    };
    let result = deduplicate_axioms(vec![f1.clone(), f2.clone()]);
    assert_eq!(result.len(), 2);
}

// ----------------------------------------------------------------------------
// Helpers
// ----------------------------------------------------------------------------

/// True iff `f` has no `Formula::Not` nodes (i.e. is already in NNF).
fn is_nnf(f: &Formula) -> bool {
    match f {
        Formula::Not(_) => false,
        Formula::And(l, r) | Formula::Or(l, r) => is_nnf(l) && is_nnf(r),
        Formula::Forall { body, .. } | Formula::Exists { body, .. } => is_nnf(body),
        _ => true,
    }
}

/// Depth of a chain `succ(succ(...(zero)...))`.  Zero base returns 0.
fn succ_chain_depth(t: &Term) -> usize {
    let mut depth = 0;
    let mut cur = t;
    loop {
        match cur {
            Term::App { function, args } if function.name == "succ" && args.len() == 1 => {
                depth += 1;
                cur = &args[0];
            }
            Term::App { function, args } if function.name == "zero" && args.is_empty() => {
                return depth;
            }
            _ => panic!("not a succ-chain: {cur:?}"),
        }
    }
}

/// True iff `f` mentions `name` as a relation symbol anywhere.
fn formula_references_relation(f: &Formula, name: &str) -> bool {
    match f {
        Formula::Atom { relation, .. } | Formula::NegAtom { relation, .. } => relation.name == name,
        Formula::And(l, r) | Formula::Or(l, r) => {
            formula_references_relation(l, name) || formula_references_relation(r, name)
        }
        Formula::Forall { body, .. } | Formula::Exists { body, .. } | Formula::Not(body) => {
            formula_references_relation(body, name)
        }
        _ => false,
    }
}

/// Build a single-theorem IR with built-in Nat sort referenced through the
/// theorem; everything else empty.
fn make_thm_ir(name: &str, conclusion: IRExpr) -> LeanIR {
    LeanIR {
        version: Some(1),
        source_file: None,
        sorts: vec![],
        constructors: vec![],
        functions: vec![],
        predicates: vec![],
        theorems: vec![IRTheorem {
            name: name.into(),
            hypotheses: vec![],
            conclusion,
        }],
        warnings: vec![],
    }
}

// Suppress unused-import warning when a particular helper isn't referenced.
#[allow(dead_code)]
fn _force_imports(_p: IRPredicate, _f: IRFunction, _s: IRSort, _h: IRHypothesis) {}
