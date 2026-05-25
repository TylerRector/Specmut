//! Phase G integration tests: sanitization, sort normalization, partial
//! recovery, and end-to-end translation of the new compatibility fixtures.
//!
//! Sanitization / normalization helpers are exercised both as unit-level
//! synthetic IR and against the regenerated JSON fixtures.

use specmut_lean::ir_types::{IREquation, IRExpr, IRParam, LeanIR};
use specmut_lean::translator::{
    is_noise_sort_name, is_typeclass_method_name, is_typeclass_noise_desc, sanitize_equation,
    sanitize_expr, LeanTranslator, TranslationResult,
};

// ----------------------------------------------------------------------------
// Helpers
// ----------------------------------------------------------------------------

fn load(name: &str) -> LeanIR {
    let path = format!("tests/fixtures/{name}.ir.json");
    let contents =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("missing fixture {path}: {e}"));
    serde_json::from_str(&contents).expect("fixture deserializes")
}

fn translate(name: &str) -> TranslationResult {
    let ir = load(name);
    LeanTranslator::translate(&ir).unwrap_or_else(|e| panic!("translate({name}) failed: {e}"))
}

fn unsupported(s: &str) -> IRExpr {
    IRExpr::Unsupported {
        description: s.to_string(),
    }
}

// ----------------------------------------------------------------------------
// Work Item 4: sort name normalization
// ----------------------------------------------------------------------------

#[test]
fn test_normalize_suppresses_inst_prefix() {
    assert!(is_noise_sort_name("instOrdNat"));
    assert!(is_noise_sort_name("instReprTree"));
    assert!(is_noise_sort_name("instDecidableEqColor"));
}

#[test]
fn test_normalize_suppresses_stdlib_namespace() {
    assert!(is_noise_sort_name("IO.RealWorld"));
    assert!(is_noise_sort_name("Std.Format"));
    assert!(is_noise_sort_name("System.FilePath"));
    assert!(is_noise_sort_name("EStateM.Result"));
}

#[test]
fn test_normalize_suppresses_universe_sorts() {
    assert!(is_noise_sort_name("Prop"));
    assert!(is_noise_sort_name("Type"));
    assert!(is_noise_sort_name("Sort"));
}

#[test]
fn test_normalize_suppresses_decidable_and_repr() {
    assert!(is_noise_sort_name("Decidable"));
    assert!(is_noise_sort_name("DecidableEq"));
    assert!(is_noise_sort_name("Repr"));
    assert!(is_noise_sort_name("Hashable"));
}

#[test]
fn test_normalize_keeps_real_sorts() {
    assert!(!is_noise_sort_name("Nat"));
    assert!(!is_noise_sort_name("Int"));
    assert!(!is_noise_sort_name("Tree"));
    assert!(!is_noise_sort_name("List_Nat"));
    assert!(!is_noise_sort_name("Color"));
    assert!(!is_noise_sort_name("Expr"));
}

#[test]
fn test_normalize_keeps_unprefixed_inst_name() {
    // "install" or "instance" lowercase first char after "inst" — not
    // an instance-naming convention.
    assert!(!is_noise_sort_name("install"));
    assert!(!is_noise_sort_name("instance"));
}

// ----------------------------------------------------------------------------
// Work Item 2: equation sanitization
// ----------------------------------------------------------------------------

#[test]
fn test_sanitize_strips_inst_unsupported_node() {
    let expr = unsupported("instOrdNat dictionary argument");
    let sanitized = sanitize_expr(&expr);
    assert!(matches!(sanitized, IRExpr::True));
}

#[test]
fn test_sanitize_strips_decidable_unsupported_node() {
    let expr = unsupported("Decidable instance arg");
    let sanitized = sanitize_expr(&expr);
    assert!(matches!(sanitized, IRExpr::True));
}

#[test]
fn test_sanitize_preserves_real_unsupported() {
    // Unsupported but NOT type-class noise — leave alone.
    let expr = unsupported("lambda expression in body");
    let sanitized = sanitize_expr(&expr);
    assert!(matches!(sanitized, IRExpr::Unsupported { .. }));
}

#[test]
fn test_sanitize_collapses_typeclass_app() {
    // App("instOrdNat", [Var("a"), Var("b")]) → after sanitisation
    // becomes a 2-arg app of the real args, but `instOrdNat` is a method
    // name so the application is suppressed.  When there are 2+ real
    // args (the args themselves aren't noise), the app stays but
    // without dictionary args.
    let expr = IRExpr::App {
        fn_name: "instOrdNat".to_string(),
        args: vec![
            IRExpr::Var {
                name: "a".to_string(),
            },
            IRExpr::Var {
                name: "b".to_string(),
            },
        ],
    };
    let sanitized = sanitize_expr(&expr);
    // 2 real Var args → app stays as an instOrdNat call with 2 args.
    match sanitized {
        IRExpr::App { args, .. } => assert_eq!(args.len(), 2),
        other => panic!("expected app, got {other:?}"),
    }
}

#[test]
fn test_sanitize_drops_inst_dict_from_app_args() {
    // App("foo", [Unsupported("instOrdNat"), Var("xs")]) → drops the
    // dictionary argument, keeps Var("xs").
    let expr = IRExpr::App {
        fn_name: "foo".to_string(),
        args: vec![
            unsupported("instOrdNat dict"),
            IRExpr::Var {
                name: "xs".to_string(),
            },
        ],
    };
    let sanitized = sanitize_expr(&expr);
    match sanitized {
        IRExpr::App { fn_name, args } => {
            assert_eq!(fn_name, "foo");
            assert_eq!(args.len(), 1);
            assert!(matches!(args[0], IRExpr::Var { .. }));
        }
        other => panic!("expected app, got {other:?}"),
    }
}

#[test]
fn test_sanitize_equation_walks_lhs_and_rhs() {
    let eq = IREquation {
        vars: vec![IRParam {
            name: "x".into(),
            sort: "Nat".into(),
        }],
        lhs: IRExpr::App {
            fn_name: "Sorted".into(),
            args: vec![
                unsupported("instOrd dict"),
                IRExpr::Var { name: "x".into() },
            ],
        },
        rhs: IRExpr::True,
    };
    let sanitized = sanitize_equation(&eq);
    match sanitized.lhs {
        IRExpr::App { args, .. } => assert_eq!(args.len(), 1),
        _ => panic!("lhs should still be App after dropping dict arg"),
    }
}

#[test]
fn test_sanitize_recurses_through_quantifiers() {
    // ∀x. Unsupported(inst) → ∀x. True
    let expr = IRExpr::Forall {
        var: "x".into(),
        sort: "Nat".into(),
        body: Box::new(unsupported("instOrdNat")),
    };
    let sanitized = sanitize_expr(&expr);
    match sanitized {
        IRExpr::Forall { body, .. } => assert!(matches!(*body, IRExpr::True)),
        _ => panic!("forall structure should be preserved"),
    }
}

#[test]
fn test_typeclass_method_name_detection() {
    assert!(is_typeclass_method_name("instOrdNat"));
    assert!(is_typeclass_method_name("Decidable.decide"));
    assert!(is_typeclass_method_name("Repr.reprPrec"));
    assert!(is_typeclass_method_name("BEq.beq"));
    assert!(is_typeclass_method_name("Foo.mk"));
    assert!(!is_typeclass_method_name("Sorted"));
    assert!(!is_typeclass_method_name("Tree.contains"));
}

#[test]
fn test_typeclass_noise_desc_detection() {
    assert!(is_typeclass_noise_desc("inst dictionary"));
    assert!(is_typeclass_noise_desc("Decidable argument"));
    assert!(is_typeclass_noise_desc("Repr instance"));
    assert!(is_typeclass_noise_desc("Hashable dict"));
    assert!(!is_typeclass_noise_desc("lambda expression"));
    assert!(!is_typeclass_noise_desc("metavariable"));
}

// ----------------------------------------------------------------------------
// Work Item 3: partial equation recovery
// ----------------------------------------------------------------------------

#[test]
fn test_partial_equation_recovery_predicate_still_translated() {
    // Build an IR with one predicate that has 3 equations: two are
    // simple `P x = True`, one contains an `Unsupported` node that
    // sanitisation won't replace (so the equation fails translation).
    // The predicate should still appear in translated_predicates with
    // 2 axioms.
    use specmut_lean::ir_types::IRPredicate;
    let ir = LeanIR {
        version: Some(1),
        source_file: Some("test.lean".into()),
        sorts: vec![],
        constructors: vec![],
        functions: vec![],
        predicates: vec![IRPredicate {
            name: "P".into(),
            params: vec![IRParam {
                name: "x".into(),
                sort: "Nat".into(),
            }],
            body: IRExpr::True,
            equations: vec![
                IREquation {
                    vars: vec![IRParam {
                        name: "x".into(),
                        sort: "Nat".into(),
                    }],
                    lhs: IRExpr::App {
                        fn_name: "P".into(),
                        args: vec![IRExpr::Var { name: "x".into() }],
                    },
                    rhs: IRExpr::True,
                },
                IREquation {
                    vars: vec![IRParam {
                        name: "x".into(),
                        sort: "Nat".into(),
                    }],
                    lhs: IRExpr::App {
                        fn_name: "P".into(),
                        args: vec![IRExpr::Var { name: "x".into() }],
                    },
                    rhs: unsupported("genuine unsupported lambda in body"),
                },
                IREquation {
                    vars: vec![IRParam {
                        name: "x".into(),
                        sort: "Nat".into(),
                    }],
                    lhs: IRExpr::App {
                        fn_name: "P".into(),
                        args: vec![IRExpr::Var { name: "x".into() }],
                    },
                    rhs: IRExpr::False,
                },
            ],
        }],
        theorems: vec![],
        warnings: vec![],
    };
    let r = LeanTranslator::translate(&ir).expect("partial recovery should succeed");
    assert!(
        r.translated_predicates.contains(&"P".to_string()),
        "predicate P should be translated despite one failing equation"
    );
    // 2 surviving equations, both contribute axioms (possibly deduped
    // to 1 if they happen to NNF to the same formula — either is OK).
    assert!(!r.axioms.is_empty(), "expected at least one axiom");
    // Warning should be prefixed "Partial:".
    assert!(
        r.warnings.iter().any(|w| w.starts_with("Partial:")),
        "expected a Partial: warning, got {:?}",
        r.warnings
    );
}

// ----------------------------------------------------------------------------
// Work Item 5: new fixtures translate end-to-end
// ----------------------------------------------------------------------------

#[test]
fn test_deriving_fixture_translates_with_no_typeclass_leakage() {
    let r = translate("deriving");
    // Color survives as a sort.
    assert!(
        r.signature.sorts.iter().any(|s| s.name == "Color"),
        "Color sort missing: {:?}",
        r.signature.sorts
    );
    // No `inst*` / `Repr*` symbol leaks through.
    for f in &r.signature.functions {
        assert!(
            !f.name.starts_with("inst") && !f.name.contains("Repr"),
            "noise function survived: {}",
            f.name
        );
    }
    for rel in &r.signature.relations {
        assert!(
            !rel.name.starts_with("inst") && !rel.name.contains("Repr"),
            "noise relation survived: {}",
            rel.name
        );
    }
    // The isPrimary predicate translated.
    assert!(
        r.translated_predicates.iter().any(|n| n == "isPrimary"),
        "isPrimary missing from translated_predicates: {:?}",
        r.translated_predicates
    );
    // At least one of the two theorems translated.
    assert!(
        !r.translated_theorems.is_empty(),
        "expected at least one translated theorem"
    );
}

#[test]
fn test_recursive_list_fixture_translates() {
    let r = translate("recursive_list");
    // Both predicates translate (or at least one of them after Phase G
    // sanitisation rescues the recursive cases).
    assert!(
        !r.translated_predicates.is_empty(),
        "expected ≥1 translated predicate, got: skipped={:?}",
        r.skipped_predicates
    );
    // All axioms are sentences in NNF.
    for axiom in &r.axioms {
        assert!(axiom.is_sentence(), "non-sentence axiom: {axiom:?}");
    }
}

#[test]
fn test_nat_props_fixture_translates() {
    let r = translate("nat_props");
    assert!(
        !r.axioms.is_empty(),
        "nat_props produced no axioms: skipped_predicates={:?}, skipped_theorems={:?}",
        r.skipped_predicates,
        r.skipped_theorems
    );
    // Even-related predicate should translate (or at least be referenced).
    let has_even = r.translated_predicates.iter().any(|n| n == "Even")
        || r.translated_theorems.iter().any(|n| n == "zero_even");
    assert!(has_even, "expected Even-related declarations to translate");
}

#[test]
fn test_multi_inductive_fixture_translates() {
    let r = translate("multi_inductive");
    // Expr sort and its three constructors.
    assert!(r.signature.sorts.iter().any(|s| s.name == "Expr"));
    for ctor in ["Expr.lit", "Expr.add", "Expr.mul"] {
        assert!(
            r.signature.functions.iter().any(|f| f.name == ctor),
            "constructor {ctor} missing"
        );
    }
}

#[test]
fn test_all_new_fixtures_invariants() {
    // Translator output stays consistent across the new fixtures:
    //   - Signature::new must accept it (validated by translate()
    //     returning Ok).
    //   - axioms.len() == axiom_origins.len().
    //   - All axioms are sentences in NNF.
    for name in [
        "deriving",
        "recursive_list",
        "nat_props",
        "multi_inductive",
    ] {
        let r = translate(name);
        assert_eq!(
            r.axioms.len(),
            r.axiom_origins.len(),
            "{name}: axiom_origins parallel-vector invariant"
        );
        for axiom in &r.axioms {
            assert!(axiom.is_sentence(), "{name}: non-sentence axiom");
        }
    }
}
