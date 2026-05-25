//! First-order formulas in negation normal form, with de Bruijn–indexed
//! variables.
//!
//! The [`Formula`] enum can transitively hold a [`Formula::Not`] node so that
//! external input (e.g. parsed `~φ`) can be represented before normalization;
//! after [`Formula::to_nnf`] has been applied, no `Not` nodes remain and
//! negation appears only at the atomic level (`NegAtom`, `Neq`).  Every other
//! module in this crate consumes formulas in NNF.
//!
//! See §3.2 of the specification document.

use std::collections::BTreeSet;

use crate::signature::{FunctionSymbol, RelationSymbol, SortSymbol};

/// A term in first-order logic.
///
/// Bound variables use de Bruijn indices: `Var(0)` is the innermost binder,
/// `Var(1)` the next outer one, and so on.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Term {
    /// de Bruijn index for a bound or free variable.
    Var(usize),
    /// Function application: f(t₁, …, tₙ).
    App {
        /// The function symbol being applied.
        function: FunctionSymbol,
        /// The arguments, in order.
        args: Vec<Term>,
    },
}

/// A first-order formula.
///
/// The canonical (post-`to_nnf`) form contains no [`Formula::Not`] nodes;
/// negation only appears as `NegAtom` / `Neq`.  The variant order chosen here
/// is the canonical ordering from §3.2:
/// `Bot < Top < Atom < NegAtom < Eq < Neq < And < Or < Forall < Exists`.
/// `Not` is declared last so that it does not perturb that ordering for
/// NNF-canonical formulas (where it never appears).
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Formula {
    /// ⊥ (false).
    Bot,
    /// ⊤ (true).
    Top,
    /// R(t₁, …, tₙ).
    Atom {
        /// The relation symbol being applied.
        relation: RelationSymbol,
        /// The arguments, in order.
        args: Vec<Term>,
    },
    /// ¬R(t₁, …, tₙ) — negation only at the atomic level.
    NegAtom {
        /// The relation symbol being applied.
        relation: RelationSymbol,
        /// The arguments, in order.
        args: Vec<Term>,
    },
    /// t₁ = t₂.
    Eq(Term, Term),
    /// t₁ ≠ t₂.
    Neq(Term, Term),
    /// φ₁ ∧ φ₂.
    And(Box<Formula>, Box<Formula>),
    /// φ₁ ∨ φ₂.
    Or(Box<Formula>, Box<Formula>),
    /// ∀x:S. φ  (binds de Bruijn index 0 in φ).
    Forall {
        /// The sort of the bound variable.
        sort: SortSymbol,
        /// The body of the quantifier.
        body: Box<Formula>,
    },
    /// ∃x:S. φ.
    Exists {
        /// The sort of the bound variable.
        sort: SortSymbol,
        /// The body of the quantifier.
        body: Box<Formula>,
    },
    /// Non-NNF general negation. Eliminated by [`Formula::to_nnf`]; should
    /// not appear in formulas consumed by the lattice or model modules.
    Not(Box<Formula>),
}

impl Formula {
    /// Convert an arbitrary formula to negation normal form by pushing
    /// negations inward (de Morgan) and eliminating double negation.
    ///
    /// The returned formula contains no [`Formula::Not`] nodes.
    pub fn to_nnf(formula: Formula) -> Formula {
        match formula {
            Formula::Not(inner) => negate(Formula::to_nnf(*inner)),
            Formula::And(l, r) => Formula::And(
                Box::new(Formula::to_nnf(*l)),
                Box::new(Formula::to_nnf(*r)),
            ),
            Formula::Or(l, r) => Formula::Or(
                Box::new(Formula::to_nnf(*l)),
                Box::new(Formula::to_nnf(*r)),
            ),
            Formula::Forall { sort, body } => Formula::Forall {
                sort,
                body: Box::new(Formula::to_nnf(*body)),
            },
            Formula::Exists { sort, body } => Formula::Exists {
                sort,
                body: Box::new(Formula::to_nnf(*body)),
            },
            other => other,
        }
    }

    /// The quantifier rank: the maximum nesting depth of quantifiers in
    /// this formula. A quantifier-free formula has rank 0.
    pub fn quantifier_rank(&self) -> usize {
        match self {
            Formula::Bot
            | Formula::Top
            | Formula::Atom { .. }
            | Formula::NegAtom { .. }
            | Formula::Eq(_, _)
            | Formula::Neq(_, _) => 0,
            Formula::And(l, r) | Formula::Or(l, r) => l.quantifier_rank().max(r.quantifier_rank()),
            Formula::Forall { body, .. } | Formula::Exists { body, .. } => {
                1 + body.quantifier_rank()
            }
            Formula::Not(inner) => inner.quantifier_rank(),
        }
    }

    /// The set of free variables, returned as de Bruijn indices interpreted
    /// at the formula's top level (i.e. depth 0).
    pub fn free_vars(&self) -> BTreeSet<usize> {
        let mut acc = BTreeSet::new();
        collect_free_vars(self, 0, &mut acc);
        acc
    }

    /// True iff the formula is a sentence (no free variables).
    pub fn is_sentence(&self) -> bool {
        self.free_vars().is_empty()
    }

    /// Substitute every free occurrence of `Var(index)` (interpreted at this
    /// formula's depth 0) with `term`, shifting de Bruijn indices as binders
    /// are crossed so that the substituted term's free variables continue to
    /// refer to the same enclosing binders.
    pub fn substitute(&self, index: usize, term: &Term) -> Formula {
        substitute_formula(self, index, term, 0)
    }

    /// Syntactic equality.  Because the representation is de Bruijn–indexed,
    /// this coincides with α-equivalence.
    pub fn alpha_eq(&self, other: &Formula) -> bool {
        self == other
    }

    /// Canonical ordering, as defined in §3.2.  Equivalent to the derived
    /// [`Ord`] impl, which is configured to match the spec's variant order.
    pub fn canonical_cmp(&self, other: &Formula) -> std::cmp::Ordering {
        self.cmp(other)
    }

    /// All atomic subformulas (positive `Atom` and negative `NegAtom`).
    ///
    /// `Eq` / `Neq` are not collected: the spec defines atoms as relation
    /// applications.
    pub fn atoms(&self) -> Vec<Formula> {
        let mut acc = Vec::new();
        collect_atoms(self, &mut acc);
        acc
    }

    /// Fold an iterator of formulas into a left-associated conjunction tree,
    /// using ⊤ as the identity element for an empty iterator.
    pub fn conjunction(formulas: impl IntoIterator<Item = Formula>) -> Formula {
        let mut iter = formulas.into_iter();
        match iter.next() {
            None => Formula::Top,
            Some(first) => iter.fold(first, |acc, f| Formula::And(Box::new(acc), Box::new(f))),
        }
    }

    /// Fold an iterator of formulas into a left-associated disjunction tree,
    /// using ⊥ as the identity element for an empty iterator.
    pub fn disjunction(formulas: impl IntoIterator<Item = Formula>) -> Formula {
        let mut iter = formulas.into_iter();
        match iter.next() {
            None => Formula::Bot,
            Some(first) => iter.fold(first, |acc, f| Formula::Or(Box::new(acc), Box::new(f))),
        }
    }
}

/// Compute the NNF negation of an already-NNF formula.
///
/// `Not` nodes inside `inner` are handled by recursing through `to_nnf` so
/// that the result is itself fully NNF.
fn negate(inner: Formula) -> Formula {
    match inner {
        Formula::Top => Formula::Bot,
        Formula::Bot => Formula::Top,
        Formula::Atom { relation, args } => Formula::NegAtom { relation, args },
        Formula::NegAtom { relation, args } => Formula::Atom { relation, args },
        Formula::Eq(a, b) => Formula::Neq(a, b),
        Formula::Neq(a, b) => Formula::Eq(a, b),
        Formula::And(l, r) => Formula::Or(Box::new(negate(*l)), Box::new(negate(*r))),
        Formula::Or(l, r) => Formula::And(Box::new(negate(*l)), Box::new(negate(*r))),
        Formula::Forall { sort, body } => Formula::Exists {
            sort,
            body: Box::new(negate(*body)),
        },
        Formula::Exists { sort, body } => Formula::Forall {
            sort,
            body: Box::new(negate(*body)),
        },
        // Double negation: ¬¬φ ⇝ φ-in-NNF.
        Formula::Not(inner) => Formula::to_nnf(*inner),
    }
}

fn collect_free_vars(f: &Formula, depth: usize, acc: &mut BTreeSet<usize>) {
    match f {
        Formula::Top | Formula::Bot => {}
        Formula::Atom { args, .. } | Formula::NegAtom { args, .. } => {
            for a in args {
                collect_term_free_vars(a, depth, acc);
            }
        }
        Formula::Eq(a, b) | Formula::Neq(a, b) => {
            collect_term_free_vars(a, depth, acc);
            collect_term_free_vars(b, depth, acc);
        }
        Formula::And(l, r) | Formula::Or(l, r) => {
            collect_free_vars(l, depth, acc);
            collect_free_vars(r, depth, acc);
        }
        Formula::Forall { body, .. } | Formula::Exists { body, .. } => {
            collect_free_vars(body, depth + 1, acc);
        }
        Formula::Not(inner) => collect_free_vars(inner, depth, acc),
    }
}

fn collect_term_free_vars(t: &Term, depth: usize, acc: &mut BTreeSet<usize>) {
    match t {
        Term::Var(i) => {
            if *i >= depth {
                acc.insert(*i - depth);
            }
        }
        Term::App { args, .. } => {
            for a in args {
                collect_term_free_vars(a, depth, acc);
            }
        }
    }
}

fn collect_atoms(f: &Formula, acc: &mut Vec<Formula>) {
    match f {
        Formula::Atom { .. } | Formula::NegAtom { .. } => acc.push(f.clone()),
        Formula::And(l, r) | Formula::Or(l, r) => {
            collect_atoms(l, acc);
            collect_atoms(r, acc);
        }
        Formula::Forall { body, .. } | Formula::Exists { body, .. } | Formula::Not(body) => {
            collect_atoms(body, acc);
        }
        Formula::Top | Formula::Bot | Formula::Eq(_, _) | Formula::Neq(_, _) => {}
    }
}

/// Recursive substitution helper.
///
/// `depth` is the number of binders we have descended through.  The target
/// of substitution at this depth is `index + depth` (since each binder
/// crossed pushes every outer variable index up by one).  When we splice
/// `term` into the body, its own free variables must be shifted up by
/// `depth` to keep referring to the same enclosing binders.
fn substitute_formula(f: &Formula, index: usize, term: &Term, depth: usize) -> Formula {
    match f {
        Formula::Top => Formula::Top,
        Formula::Bot => Formula::Bot,
        Formula::Atom { relation, args } => Formula::Atom {
            relation: relation.clone(),
            args: args
                .iter()
                .map(|a| substitute_term(a, index, term, depth))
                .collect(),
        },
        Formula::NegAtom { relation, args } => Formula::NegAtom {
            relation: relation.clone(),
            args: args
                .iter()
                .map(|a| substitute_term(a, index, term, depth))
                .collect(),
        },
        Formula::Eq(a, b) => Formula::Eq(
            substitute_term(a, index, term, depth),
            substitute_term(b, index, term, depth),
        ),
        Formula::Neq(a, b) => Formula::Neq(
            substitute_term(a, index, term, depth),
            substitute_term(b, index, term, depth),
        ),
        Formula::And(l, r) => Formula::And(
            Box::new(substitute_formula(l, index, term, depth)),
            Box::new(substitute_formula(r, index, term, depth)),
        ),
        Formula::Or(l, r) => Formula::Or(
            Box::new(substitute_formula(l, index, term, depth)),
            Box::new(substitute_formula(r, index, term, depth)),
        ),
        Formula::Forall { sort, body } => Formula::Forall {
            sort: sort.clone(),
            body: Box::new(substitute_formula(body, index, term, depth + 1)),
        },
        Formula::Exists { sort, body } => Formula::Exists {
            sort: sort.clone(),
            body: Box::new(substitute_formula(body, index, term, depth + 1)),
        },
        Formula::Not(inner) => Formula::Not(Box::new(substitute_formula(inner, index, term, depth))),
    }
}

fn substitute_term(t: &Term, index: usize, term: &Term, depth: usize) -> Term {
    match t {
        Term::Var(i) => {
            if *i == index + depth {
                shift_term(term, depth)
            } else {
                Term::Var(*i)
            }
        }
        Term::App { function, args } => Term::App {
            function: function.clone(),
            args: args
                .iter()
                .map(|a| substitute_term(a, index, term, depth))
                .collect(),
        },
    }
}

fn shift_term(t: &Term, by: usize) -> Term {
    match t {
        Term::Var(i) => Term::Var(i + by),
        Term::App { function, args } => Term::App {
            function: function.clone(),
            args: args.iter().map(|a| shift_term(a, by)).collect(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(name: &str) -> SortSymbol {
        SortSymbol::new(name)
    }

    fn rel(name: &str, arity: Vec<SortSymbol>) -> RelationSymbol {
        RelationSymbol::new(name, arity)
    }

    fn atom(name: &str, args: Vec<Term>) -> Formula {
        let arity: Vec<SortSymbol> = args.iter().map(|_| s("S")).collect();
        Formula::Atom {
            relation: rel(name, arity),
            args,
        }
    }

    fn neg_atom(name: &str, args: Vec<Term>) -> Formula {
        let arity: Vec<SortSymbol> = args.iter().map(|_| s("S")).collect();
        Formula::NegAtom {
            relation: rel(name, arity),
            args,
        }
    }

    #[test]
    fn to_nnf_pushes_negation_through_forall() {
        // ¬(∀x:S. P(x))  ⇝  ∃x:S. ¬P(x)
        let phi = Formula::Not(Box::new(Formula::Forall {
            sort: s("S"),
            body: Box::new(atom("P", vec![Term::Var(0)])),
        }));
        let nnf = Formula::to_nnf(phi);
        let expected = Formula::Exists {
            sort: s("S"),
            body: Box::new(neg_atom("P", vec![Term::Var(0)])),
        };
        assert_eq!(nnf, expected);
    }

    #[test]
    fn to_nnf_de_morgan_conjunction() {
        // ¬(P ∧ Q)  ⇝  (¬P) ∨ (¬Q)
        let phi = Formula::Not(Box::new(Formula::And(
            Box::new(atom("P", vec![])),
            Box::new(atom("Q", vec![])),
        )));
        let nnf = Formula::to_nnf(phi);
        let expected = Formula::Or(
            Box::new(neg_atom("P", vec![])),
            Box::new(neg_atom("Q", vec![])),
        );
        assert_eq!(nnf, expected);
    }

    #[test]
    fn to_nnf_eliminates_double_negation() {
        // ¬¬P  ⇝  P
        let phi = Formula::Not(Box::new(Formula::Not(Box::new(atom("P", vec![])))));
        assert_eq!(Formula::to_nnf(phi), atom("P", vec![]));
    }

    #[test]
    fn to_nnf_double_negation_on_quantifier() {
        // ¬¬(∀x. P(x))  ⇝  ∀x. P(x)
        let inner = Formula::Forall {
            sort: s("S"),
            body: Box::new(atom("P", vec![Term::Var(0)])),
        };
        let phi = Formula::Not(Box::new(Formula::Not(Box::new(inner.clone()))));
        assert_eq!(Formula::to_nnf(phi), inner);
    }

    #[test]
    fn quantifier_rank_counts_nesting() {
        // ∀x. ∃y. P(x, y)  has rank 2.
        let inner = atom("P", vec![Term::Var(1), Term::Var(0)]);
        let phi = Formula::Forall {
            sort: s("S"),
            body: Box::new(Formula::Exists {
                sort: s("S"),
                body: Box::new(inner),
            }),
        };
        assert_eq!(phi.quantifier_rank(), 2);
    }

    #[test]
    fn quantifier_rank_disjunction_takes_max() {
        // (∀x. P(x)) ∨ Q  has rank 1.
        let phi = Formula::Or(
            Box::new(Formula::Forall {
                sort: s("S"),
                body: Box::new(atom("P", vec![Term::Var(0)])),
            }),
            Box::new(atom("Q", vec![])),
        );
        assert_eq!(phi.quantifier_rank(), 1);
    }

    #[test]
    fn free_vars_of_open_formula_under_quantifier() {
        // ∀x. P(x, y)  where x = Var(0), y = Var(1) under the binder.
        // At the top level, the binder shadows index 0, so the free index of
        // y is 1 - 1 = 0.
        let phi = Formula::Forall {
            sort: s("S"),
            body: Box::new(atom("P", vec![Term::Var(0), Term::Var(1)])),
        };
        let fv = phi.free_vars();
        let mut expected = BTreeSet::new();
        expected.insert(0);
        assert_eq!(fv, expected);
    }

    #[test]
    fn free_vars_of_closed_formula_is_empty() {
        // ∀x. P(x)
        let phi = Formula::Forall {
            sort: s("S"),
            body: Box::new(atom("P", vec![Term::Var(0)])),
        };
        assert!(phi.free_vars().is_empty());
        assert!(phi.is_sentence());
    }

    #[test]
    fn is_sentence_detects_free_variable() {
        // P(y) with y = Var(0) free.
        let phi = atom("P", vec![Term::Var(0)]);
        assert!(!phi.is_sentence());
        let mut expected = BTreeSet::new();
        expected.insert(0);
        assert_eq!(phi.free_vars(), expected);
    }

    #[test]
    fn substitute_shifts_under_binder() {
        // φ = ∀x:S. P(x, y)            where y = Var(1) inside the binder
        //                              i.e. de Bruijn index 0 at the top.
        // φ[y := f(z)]  with z = Var(0) at the top
        // Result: ∀x:S. P(x, f(z'))    where z' = Var(1) inside the binder
        //                              (shifted up by 1 because we crossed
        //                              the universal binder).
        let f_sym = FunctionSymbol::new("f", vec![s("S")], s("S"));
        let phi = Formula::Forall {
            sort: s("S"),
            body: Box::new(atom("P", vec![Term::Var(0), Term::Var(1)])),
        };
        let replacement = Term::App {
            function: f_sym.clone(),
            args: vec![Term::Var(0)],
        };
        let result = phi.substitute(0, &replacement);
        let expected = Formula::Forall {
            sort: s("S"),
            body: Box::new(atom(
                "P",
                vec![
                    Term::Var(0),
                    Term::App {
                        function: f_sym,
                        args: vec![Term::Var(1)],
                    },
                ],
            )),
        };
        assert_eq!(result, expected);
    }

    #[test]
    fn substitute_replaces_top_level_variable() {
        // P(y)[y := c]  ⇝  P(c)   where c is a constant (Var-free term).
        let c = Term::App {
            function: FunctionSymbol::new("c", vec![], s("S")),
            args: vec![],
        };
        let phi = atom("P", vec![Term::Var(0)]);
        let result = phi.substitute(0, &c);
        assert_eq!(result, atom("P", vec![c]));
    }

    #[test]
    fn substitute_leaves_other_variables_alone() {
        // P(y, z)[y := c]  ⇝  P(c, z)
        let c = Term::App {
            function: FunctionSymbol::new("c", vec![], s("S")),
            args: vec![],
        };
        let phi = atom("P", vec![Term::Var(0), Term::Var(1)]);
        let result = phi.substitute(0, &c);
        assert_eq!(result, atom("P", vec![c, Term::Var(1)]));
    }

    #[test]
    fn conjunction_empty_is_top_disjunction_empty_is_bot() {
        assert_eq!(Formula::conjunction(std::iter::empty()), Formula::Top);
        assert_eq!(Formula::disjunction(std::iter::empty()), Formula::Bot);
    }

    #[test]
    fn conjunction_single_is_identity() {
        let p = atom("P", vec![]);
        assert_eq!(Formula::conjunction([p.clone()]), p);
    }

    #[test]
    fn atoms_collects_atomic_subformulas() {
        let p = atom("P", vec![]);
        let q = neg_atom("Q", vec![]);
        let phi = Formula::And(Box::new(p.clone()), Box::new(q.clone()));
        let atoms = phi.atoms();
        assert_eq!(atoms, vec![p, q]);
    }

    #[test]
    fn canonical_order_matches_spec() {
        // Bot < Top < Atom < NegAtom < Eq < Neq < And < Or < Forall < Exists
        let bot = Formula::Bot;
        let top = Formula::Top;
        let a = atom("P", vec![]);
        let na = neg_atom("P", vec![]);
        let eq = Formula::Eq(Term::Var(0), Term::Var(0));
        let neq = Formula::Neq(Term::Var(0), Term::Var(0));
        let and = Formula::And(Box::new(Formula::Top), Box::new(Formula::Top));
        let or = Formula::Or(Box::new(Formula::Top), Box::new(Formula::Top));
        let fa = Formula::Forall {
            sort: s("S"),
            body: Box::new(Formula::Top),
        };
        let ex = Formula::Exists {
            sort: s("S"),
            body: Box::new(Formula::Top),
        };
        let ordered = [bot, top, a, na, eq, neq, and, or, fa, ex];
        for w in ordered.windows(2) {
            assert!(w[0] < w[1], "{:?} should sort before {:?}", w[0], w[1]);
        }
    }
}
