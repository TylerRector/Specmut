//! Finite Σ-structures and an exhaustive enumerator.
//!
//! A [`FiniteModel`] is a finite first-order structure: each sort is
//! interpreted as an integer carrier `{0, 1, …, n − 1}`, each function
//! symbol as a total lookup table on tuples of carrier indices, and each
//! relation symbol as a subset of the appropriate tuple space.
//!
//! See §3.3 of the specification document.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;

use crate::formula::{Formula, Term};
use crate::signature::{RelationSymbol, Signature, SortSymbol};

/// A finite Σ-structure.
///
/// INVARIANT: Every sort in `signature.sorts` has a strictly positive
/// cardinality in `carriers` (no empty carrier sets).
/// INVARIANT: `function_interps[f]` is a total map from `domain(f)`-tuples
/// of carrier indices to indices in the carrier of `codomain(f)`.
/// INVARIANT: `relation_interps[r]` ⊆ ∏ carriers(arity(r)) (every tuple
/// references valid carrier indices).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FiniteModel {
    /// The signature this model interprets.
    pub signature: Signature,
    /// Cardinality of each sort's carrier (elements are indices `[0, n)`).
    pub carriers: BTreeMap<SortSymbol, usize>,
    /// Function interpretations: function name → arg-tuple → result index.
    pub function_interps: BTreeMap<String, BTreeMap<Vec<usize>, usize>>,
    /// Relation interpretations: relation name → set of holding tuples.
    pub relation_interps: BTreeMap<String, BTreeSet<Vec<usize>>>,
}

impl FiniteModel {
    /// Evaluate a closed formula (sentence) in this model.
    ///
    /// REQUIRES: `formula.is_sentence() == true`.
    /// REQUIRES: every relation / function symbol referenced in `formula`
    /// is interpreted in `self`.
    pub fn evaluate(&self, formula: &Formula) -> bool {
        debug_assert!(formula.is_sentence(), "evaluate requires a sentence");
        self.evaluate_with_assignment(formula, &[])
    }

    /// Evaluate a formula under an explicit assignment of de Bruijn indices
    /// to carrier elements.  `assignment[i]` binds `Var(i)`.
    pub fn evaluate_with_assignment(&self, formula: &Formula, assignment: &[usize]) -> bool {
        match formula {
            Formula::Top => true,
            Formula::Bot => false,
            Formula::Atom { relation, args } => {
                let tuple = self.eval_args(args, assignment);
                self.relation_holds(&relation.name, &tuple)
            }
            Formula::NegAtom { relation, args } => {
                let tuple = self.eval_args(args, assignment);
                !self.relation_holds(&relation.name, &tuple)
            }
            Formula::Eq(a, b) => self.eval_term(a, assignment) == self.eval_term(b, assignment),
            Formula::Neq(a, b) => self.eval_term(a, assignment) != self.eval_term(b, assignment),
            Formula::And(l, r) => {
                self.evaluate_with_assignment(l, assignment)
                    && self.evaluate_with_assignment(r, assignment)
            }
            Formula::Or(l, r) => {
                self.evaluate_with_assignment(l, assignment)
                    || self.evaluate_with_assignment(r, assignment)
            }
            Formula::Not(inner) => !self.evaluate_with_assignment(inner, assignment),
            Formula::Forall { sort, body } => {
                let n = self.carrier_size(sort);
                (0..n).all(|i| {
                    let extended = push_assignment(assignment, i);
                    self.evaluate_with_assignment(body, &extended)
                })
            }
            Formula::Exists { sort, body } => {
                let n = self.carrier_size(sort);
                (0..n).any(|i| {
                    let extended = push_assignment(assignment, i);
                    self.evaluate_with_assignment(body, &extended)
                })
            }
        }
    }

    /// True iff every axiom in `spec` evaluates to `true` in this model.
    pub fn satisfies_spec(&self, spec: &[Formula]) -> bool {
        spec.iter().all(|f| self.evaluate(f))
    }

    /// The maximum carrier cardinality across all sorts.  Returns 0 for the
    /// degenerate case of no sorts.
    pub fn domain_size(&self) -> usize {
        self.carriers.values().copied().max().unwrap_or(0)
    }

    fn eval_args(&self, args: &[Term], assignment: &[usize]) -> Vec<usize> {
        args.iter().map(|a| self.eval_term(a, assignment)).collect()
    }

    fn eval_term(&self, t: &Term, assignment: &[usize]) -> usize {
        match t {
            Term::Var(i) => {
                debug_assert!(
                    *i < assignment.len(),
                    "unbound de Bruijn index {i} for assignment of length {}",
                    assignment.len()
                );
                assignment[*i]
            }
            Term::App { function, args } => {
                let arg_vals = self.eval_args(args, assignment);
                // Robustness: if the function symbol isn't in this model's
                // interpretation (mismatched signature) or the argument tuple
                // lies outside the interpreted domain (arity mismatch, or a
                // sub-term producing an out-of-range value), fall back to
                // element 0 rather than panicking.  This keeps tightness
                // analysis usable on Lean-translated specs where arity drift
                // between declared functions and call-site argument lists
                // can produce keys the table doesn't cover.  See the Phase D
                // §7.5 hardening note.
                self.function_interps
                    .get(&function.name)
                    .and_then(|table| table.get(&arg_vals).copied())
                    .unwrap_or(0)
            }
        }
    }

    fn relation_holds(&self, name: &str, tuple: &[usize]) -> bool {
        match self.relation_interps.get(name) {
            Some(set) => set.contains(tuple),
            None => false,
        }
    }

    fn carrier_size(&self, sort: &SortSymbol) -> usize {
        *self
            .carriers
            .get(sort)
            .expect("every sort referenced by the formula must be interpreted")
    }
}

fn push_assignment(assignment: &[usize], new_innermost: usize) -> Vec<usize> {
    let mut extended = Vec::with_capacity(assignment.len() + 1);
    extended.push(new_innermost);
    extended.extend_from_slice(assignment);
    extended
}

/// Exhaustive enumeration of Σ-structures.
///
/// The enumerator emits every combination of relation interpretations
/// (each relation laid out as a bitvector over its tuple space) crossed
/// with every combination of function interpretations (each function
/// laid out as a full lookup table from input tuples to codomain
/// elements).  No isomorphism elimination is performed.
///
/// Phase 5 bugfix: function-symbol enumeration was added so that
/// specifications mentioning functions (e.g. `output : Elem -> Elem` in
/// the sorting spec) can actually be evaluated.  Previously the
/// enumerator produced models with empty `function_interps`, which made
/// `FiniteModel::evaluate` panic on any term containing a function
/// application.
pub struct ModelEnumerator {
    signature: Signature,
    domain_size: usize,
}

impl ModelEnumerator {
    /// Construct an enumerator over `signature` with the given carrier size.
    ///
    /// `domain_size` is the cardinality used for every sort.  Phase 1 fixes
    /// a single size rather than iterating `1..=max`; future phases will
    /// generalize this.
    pub fn new(signature: Signature, domain_size: usize) -> Self {
        Self {
            signature,
            domain_size,
        }
    }

    /// Iterator over every Σ-structure with the configured carrier size.
    ///
    /// Models are produced in canonical order: relation interpretations are
    /// laid out as a single bitvector (relations sorted by name; tuples
    /// within each relation in lexicographic order), and bitvectors are
    /// emitted in numerical-equivalent lexicographic order.
    pub fn enumerate(&self) -> impl Iterator<Item = FiniteModel> {
        enumerate_at_size(&self.signature, self.domain_size).into_iter()
    }

    /// Number of distinct models without materializing them.
    ///
    /// `signature.model_space_size(n)` counts only relation
    /// interpretations; this method multiplies in the function-table
    /// space so the result actually matches what [`Self::enumerate`]
    /// produces.
    pub fn count(&self) -> BigUint {
        let mut total = self.signature.model_space_size(self.domain_size);
        let n = BigUint::from(self.domain_size);
        for f in &self.signature.functions {
            let inputs = self
                .domain_size
                .checked_pow(u32::try_from(f.domain.len()).unwrap_or(u32::MAX))
                .unwrap_or(usize::MAX);
            total *= n.pow(u32::try_from(inputs).unwrap_or(u32::MAX));
        }
        total
    }
}

fn enumerate_at_size(sig: &Signature, n: usize) -> Vec<FiniteModel> {
    if n == 0 {
        // Empty carriers violate MODEL-01.
        return Vec::new();
    }

    let carriers: BTreeMap<SortSymbol, usize> =
        sig.sorts.iter().map(|s| (s.clone(), n)).collect();

    let relation_options = enumerate_relation_interps(sig, n);
    let function_options = enumerate_function_interps(sig, n);

    // Cartesian product: relations are the outer dimension so a
    // relation-only signature (function_options.len() == 1) emits models
    // in the same canonical order as the Phase 1 enumerator.
    let mut models = Vec::with_capacity(relation_options.len() * function_options.len());
    for relations in &relation_options {
        for functions in &function_options {
            models.push(FiniteModel {
                signature: sig.clone(),
                carriers: carriers.clone(),
                function_interps: functions.clone(),
                relation_interps: relations.clone(),
            });
        }
    }
    models
}

fn enumerate_relation_interps(
    sig: &Signature,
    n: usize,
) -> Vec<BTreeMap<String, BTreeSet<Vec<usize>>>> {
    let relations: Vec<&RelationSymbol> = sig.relations.iter().collect();
    let mut bit_offsets: Vec<usize> = Vec::with_capacity(relations.len() + 1);
    bit_offsets.push(0);
    for r in &relations {
        let tuple_count = pow_usize(n, r.arity.len());
        let next = bit_offsets
            .last()
            .copied()
            .expect("seeded with one element")
            + tuple_count;
        bit_offsets.push(next);
    }
    let total_bits = *bit_offsets.last().expect("at least one offset");

    assert!(
        total_bits <= 64,
        "relation-interpretation bitvector of {total_bits} bits exceeds enumerator limit"
    );

    let total: u64 = 1u64 << total_bits;
    let mut out = Vec::with_capacity(total as usize);
    for bits in 0..total {
        let mut relation_interps: BTreeMap<String, BTreeSet<Vec<usize>>> = BTreeMap::new();
        for (i, r) in relations.iter().enumerate() {
            let arity = r.arity.len();
            let tuple_count = pow_usize(n, arity);
            let mut tuples: BTreeSet<Vec<usize>> = BTreeSet::new();
            for t in 0..tuple_count {
                let bit_idx = bit_offsets[i] + t;
                if (bits >> bit_idx) & 1 == 1 {
                    tuples.insert(int_to_tuple(t, arity, n));
                }
            }
            relation_interps.insert(r.name.clone(), tuples);
        }
        out.push(relation_interps);
    }
    out
}

fn enumerate_function_interps(
    sig: &Signature,
    n: usize,
) -> Vec<BTreeMap<String, BTreeMap<Vec<usize>, usize>>> {
    // Build per-function table-space, then take the Cartesian product
    // across all functions.  Each table is a full mapping from
    // `n^arity` input tuples to one of `n` outputs.
    let mut combinations: Vec<BTreeMap<String, BTreeMap<Vec<usize>, usize>>> =
        vec![BTreeMap::new()];
    for f in &sig.functions {
        let arity = f.domain.len();
        let input_count = pow_usize(n, arity);
        let table_count = pow_usize(n, input_count);
        let mut next: Vec<BTreeMap<String, BTreeMap<Vec<usize>, usize>>> =
            Vec::with_capacity(combinations.len() * table_count);
        for combo in &combinations {
            for table_idx in 0..table_count {
                let mut table: BTreeMap<Vec<usize>, usize> = BTreeMap::new();
                let mut remaining = table_idx;
                // Iterate inputs in lex order; the lowest-significance
                // digit fills input 0's output, etc.  Different ordering
                // is fine for correctness — count is what matters.
                for input in 0..input_count {
                    let output = remaining % n;
                    remaining /= n;
                    table.insert(int_to_tuple(input, arity, n), output);
                }
                let mut extended = combo.clone();
                extended.insert(f.name.clone(), table);
                next.push(extended);
            }
        }
        combinations = next;
    }
    combinations
}

/// Decode a tuple index into an `arity`-length tuple in base `base`.
/// Position 0 is the most significant digit so that numerical-order
/// iteration produces lexicographically ordered tuples.
fn int_to_tuple(mut idx: usize, arity: usize, base: usize) -> Vec<usize> {
    let mut tuple = vec![0usize; arity];
    for i in (0..arity).rev() {
        tuple[i] = idx % base;
        idx /= base;
    }
    tuple
}

fn pow_usize(base: usize, exp: usize) -> usize {
    let mut r = 1usize;
    for _ in 0..exp {
        r = r.checked_mul(base).expect("tuple count fits in usize");
    }
    r
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::signature::{RelationSymbol, Signature, SortSymbol};

    fn sort(name: &str) -> SortSymbol {
        SortSymbol::new(name)
    }

    fn unary_sig() -> Signature {
        let s = sort("S");
        Signature::new(
            vec![s.clone()],
            vec![],
            vec![RelationSymbol::new("P", vec![s])],
        )
        .expect("valid sig")
    }

    fn binary_sig() -> Signature {
        let s = sort("S");
        Signature::new(
            vec![s.clone()],
            vec![],
            vec![RelationSymbol::new("R", vec![s.clone(), s])],
        )
        .expect("valid sig")
    }

    fn make_model(sig: Signature, n: usize, p_tuples: Vec<Vec<usize>>) -> FiniteModel {
        let carriers: BTreeMap<SortSymbol, usize> =
            sig.sorts.iter().map(|s| (s.clone(), n)).collect();
        let mut relation_interps: BTreeMap<String, BTreeSet<Vec<usize>>> = BTreeMap::new();
        for r in &sig.relations {
            relation_interps.insert(r.name.clone(), BTreeSet::new());
        }
        let first_rel = sig
            .relations
            .iter()
            .next()
            .expect("at least one relation")
            .name
            .clone();
        let tuples_set: BTreeSet<Vec<usize>> = p_tuples.into_iter().collect();
        relation_interps.insert(first_rel, tuples_set);
        FiniteModel {
            signature: sig,
            carriers,
            function_interps: BTreeMap::new(),
            relation_interps,
        }
    }

    fn p_atom(args: Vec<Term>) -> Formula {
        let s = sort("S");
        Formula::Atom {
            relation: RelationSymbol::new("P", vec![s; args.len()]),
            args,
        }
    }

    fn r_atom(args: Vec<Term>) -> Formula {
        let s = sort("S");
        Formula::Atom {
            relation: RelationSymbol::new("R", vec![s; args.len()]),
            args,
        }
    }

    #[test]
    fn forall_holds_when_relation_is_full() {
        // Domain {0, 1}, P = {0, 1}.  ∀x. P(x) holds.
        let model = make_model(unary_sig(), 2, vec![vec![0], vec![1]]);
        let phi = Formula::Forall {
            sort: sort("S"),
            body: Box::new(p_atom(vec![Term::Var(0)])),
        };
        assert!(model.evaluate(&phi));
    }

    #[test]
    fn forall_fails_when_relation_is_partial() {
        // Domain {0, 1}, P = {0}.  ∀x. P(x) does not hold (P(1) is false).
        let model = make_model(unary_sig(), 2, vec![vec![0]]);
        let phi = Formula::Forall {
            sort: sort("S"),
            body: Box::new(p_atom(vec![Term::Var(0)])),
        };
        assert!(!model.evaluate(&phi));
    }

    #[test]
    fn exists_forall_on_total_row() {
        // Domain {0, 1}.  R = {(0,0), (0,1)}.  ∃x. ∀y. R(x,y) holds (x=0).
        let model = make_model(
            binary_sig(),
            2,
            vec![vec![0, 0], vec![0, 1]],
        );
        // ∃x:S. ∀y:S. R(x, y).  Inside the outer binder, x = Var(1).
        // Inside the inner binder, y = Var(0), x = Var(1).
        let phi = Formula::Exists {
            sort: sort("S"),
            body: Box::new(Formula::Forall {
                sort: sort("S"),
                body: Box::new(r_atom(vec![Term::Var(1), Term::Var(0)])),
            }),
        };
        assert!(model.evaluate(&phi));
    }

    #[test]
    fn exists_forall_fails_when_no_full_row() {
        // Domain {0, 1}.  R = {(0,0), (1,1)} — each row has a hole.
        let model = make_model(binary_sig(), 2, vec![vec![0, 0], vec![1, 1]]);
        let phi = Formula::Exists {
            sort: sort("S"),
            body: Box::new(Formula::Forall {
                sort: sort("S"),
                body: Box::new(r_atom(vec![Term::Var(1), Term::Var(0)])),
            }),
        };
        assert!(!model.evaluate(&phi));
    }

    #[test]
    fn satisfies_spec_requires_all_axioms() {
        // Domain {0, 1}, P = {0, 1}.
        let model = make_model(unary_sig(), 2, vec![vec![0], vec![1]]);
        let p_for_all = Formula::Forall {
            sort: sort("S"),
            body: Box::new(p_atom(vec![Term::Var(0)])),
        };
        let p_exists = Formula::Exists {
            sort: sort("S"),
            body: Box::new(p_atom(vec![Term::Var(0)])),
        };
        assert!(model.satisfies_spec(&[p_for_all.clone(), p_exists.clone()]));

        // Now drop one element from P: ∀ no longer holds.
        let model2 = make_model(unary_sig(), 2, vec![vec![0]]);
        assert!(!model2.satisfies_spec(&[p_for_all]));
        assert!(model2.satisfies_spec(&[p_exists]));
    }

    #[test]
    fn enumerator_count_unary_relation_domain_two_is_four() {
        let enumerator = ModelEnumerator::new(unary_sig(), 2);
        assert_eq!(enumerator.count(), BigUint::from(4u32));
        let models: Vec<_> = enumerator.enumerate().collect();
        assert_eq!(models.len(), 4);
    }

    #[test]
    fn enumerator_count_binary_relation_domain_two_is_sixteen() {
        let enumerator = ModelEnumerator::new(binary_sig(), 2);
        assert_eq!(enumerator.count(), BigUint::from(16u32));
        let models: Vec<_> = enumerator.enumerate().collect();
        assert_eq!(models.len(), 16);
    }

    #[test]
    fn enumerator_produces_distinct_models() {
        use std::collections::HashSet;
        let models: Vec<_> = ModelEnumerator::new(unary_sig(), 2).enumerate().collect();
        let unique: HashSet<_> = models.iter().cloned().collect();
        assert_eq!(unique.len(), models.len());
    }

    #[test]
    fn enumerator_first_model_is_empty_relation() {
        // The canonical-first model has every bit zero, i.e. P = ∅.
        let mut iter = ModelEnumerator::new(unary_sig(), 2).enumerate();
        let first = iter.next().expect("at least one model");
        let p = first.relation_interps.get("P").expect("P interpreted");
        assert!(p.is_empty());
    }

    #[test]
    fn negation_evaluates_consistently_with_atom() {
        let model = make_model(unary_sig(), 2, vec![vec![0]]);
        let p_one = p_atom(vec![Term::Var(0)]);
        // Substitute Var(0) with the concrete constant... we have no
        // constants, so just check ∃x. ¬P(x) is true (P(1) is false).
        let phi = Formula::Exists {
            sort: sort("S"),
            body: Box::new(Formula::NegAtom {
                relation: match &p_one {
                    Formula::Atom { relation, .. } => relation.clone(),
                    _ => unreachable!(),
                },
                args: vec![Term::Var(0)],
            }),
        };
        assert!(model.evaluate(&phi));
    }
}
