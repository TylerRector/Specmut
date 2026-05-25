//! The specification lattice and its supporting types.
//!
//! See §3.4 of the specification document.
//!
//! # Ordering convention
//!
//! Within this module, `leq(a, b)` is true iff `b` entails `a` — i.e. every
//! model of `b` is a model of `a`, equivalently `Mod(b) ⊆ Mod(a)`, "b is
//! stronger than a".  Under that convention:
//!
//! * `bottom` is the *empty* spec (the tautology, satisfied by every model);
//!   it is the least element because every other spec entails the empty
//!   spec vacuously.
//! * `top` is the *inconsistent* spec (axiom `⊥`, satisfied by no model);
//!   it is the greatest element because the inconsistent spec is entailed
//!   only by itself, while it itself entails everything vacuously.
//! * `meet(a, b)` is `a.axioms ∪ b.axioms` — the conjunction, which is
//!   stronger than (i.e. above, in our order) both `a` and `b`.
//! * `join(a, b)` is approximated by `a.axioms ∩ b.axioms` — the axioms
//!   shared by both, a weaker spec entailed by both.
//!
//! This matches the LATTICE-01 … LATTICE-04 invariants from §9.1 and the
//! prompt's tests (`leq(bottom, x)` for all `x`, `meet.axioms = a ∪ b`).
//! The §3.4 doc comments label `bottom` / `top` the opposite way; we treat
//! that as a typo in the spec text.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::hash::{Hash, Hasher};

use thiserror::Error;

use crate::formula::{Formula, Term};
use crate::metric::JaccardMetric;
use crate::model::FiniteModel;
use crate::signature::{RelationSymbol, Signature, SortSymbol};

/// Trait abstracting over entailment-checking strategies.
///
/// `entails(stronger, weaker)` answers: do all axioms in `stronger`
/// together entail all axioms in `weaker`?  In semantic terms,
/// `Mod(stronger) ⊆ Mod(weaker)`.
pub trait EntailmentChecker: Send + Sync {
    /// True iff every model of `stronger` is also a model of `weaker`.
    fn entails(&self, stronger: &[Formula], weaker: &[Formula]) -> bool;
}

/// Entailment-by-enumeration: check whether every model of `stronger`
/// (drawn from a fixed pre-enumerated list) also satisfies `weaker`.
pub struct ModelEntailmentChecker {
    models: Vec<FiniteModel>,
}

impl ModelEntailmentChecker {
    /// Build a checker over the given model list.
    pub fn new(models: Vec<FiniteModel>) -> Self {
        Self { models }
    }
}

impl EntailmentChecker for ModelEntailmentChecker {
    fn entails(&self, stronger: &[Formula], weaker: &[Formula]) -> bool {
        self.models
            .iter()
            .all(|m| !m.satisfies_spec(stronger) || m.satisfies_spec(weaker))
    }
}

/// An element of the specification lattice.
///
/// A `SpecElement` is identified up to logical equivalence by its
/// [`canonical_key`](SpecElement::canonical_key) — the concatenation of
/// every axiom's byte serialization (§4.1) after that serialization has
/// been deterministically sorted.  `PartialEq`, `Eq`, and `Hash` are all
/// defined in terms of the canonical key.
///
/// The `axioms` field is normalized at construction time: every axiom is
/// passed through `Formula::to_nnf` and then through `canonicalize_tree`,
/// which reorders `And` / `Or` children by their serialized bytes.
#[derive(Debug, Clone)]
pub struct SpecElement {
    /// The normalized axioms whose deductive closure defines this spec.
    pub axioms: BTreeSet<Formula>,
    canonical_key: Vec<u8>,
}

impl SpecElement {
    /// Construct a new element from a set of axioms, normalizing them in
    /// place and computing the canonical key.
    pub fn new(axioms: BTreeSet<Formula>) -> Self {
        let normalized: BTreeSet<Formula> = axioms
            .into_iter()
            .map(|f| canonicalize_tree(Formula::to_nnf(f)))
            .collect();
        let mut serialized: Vec<Vec<u8>> = normalized
            .iter()
            .map(Self::canonical_serialize)
            .collect();
        serialized.sort();
        let canonical_key: Vec<u8> = serialized.into_iter().flatten().collect();
        Self {
            axioms: normalized,
            canonical_key,
        }
    }

    /// The canonical byte serialization of this element's axiom set.  Two
    /// `SpecElement`s with identical canonical keys are equivalent under
    /// the normalization pipeline.
    pub fn canonical_key(&self) -> &[u8] {
        &self.canonical_key
    }

    /// Serialize a single formula according to the canonical byte format
    /// defined in §4.1.  `And` and `Or` children are emitted in
    /// lexicographic order on their own serializations, so that two
    /// α-equivalent formulas differing only in argument order produce
    /// identical bytes.
    pub fn canonical_serialize(formula: &Formula) -> Vec<u8> {
        let mut out = Vec::new();
        serialize_formula(formula, &mut out);
        out
    }

    /// Convenience for callers that hold a `Vec<Formula>` and want a
    /// canonicalized element.
    pub fn from_axioms(axioms: impl IntoIterator<Item = Formula>) -> Self {
        Self::new(axioms.into_iter().collect())
    }
}

impl PartialEq for SpecElement {
    fn eq(&self, other: &Self) -> bool {
        self.canonical_key == other.canonical_key
    }
}

impl Eq for SpecElement {}

impl Hash for SpecElement {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.canonical_key.hash(state);
    }
}

/// Errors that can arise while building a [`SpecLattice`].
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum LatticeConstructionError {
    /// The local construction produced more candidate elements before
    /// ε-filtering than the configured budget allowed.
    #[error(
        "local lattice generated {generated} candidates, exceeding budget {limit} before ε-filtering"
    )]
    TooManyCandidates {
        /// Number of candidates considered.
        generated: usize,
        /// The configured maximum.
        limit: usize,
    },
}

/// The specification lattice — for now built only locally around a center
/// element (see [`SpecLattice::build_local`]).  The full lattice
/// construction described in §3.4 is left for a later phase.
pub struct SpecLattice {
    signature: Signature,
    quantifier_rank: usize,
    elements: Vec<SpecElement>,
    /// `leq_matrix[i][j]` = `i ≤ j` = "j entails i".
    leq_matrix: Vec<Vec<bool>>,
    /// `hasse[i]` = indices that cover `i` (immediate successors above).
    hasse: Vec<Vec<usize>>,
    /// Canonical key → element index.
    index: HashMap<Vec<u8>, usize>,
    /// Index of the empty spec (least element).
    bottom: usize,
    /// Index of the inconsistent spec (greatest element).
    top: usize,
}

const DEFAULT_CANDIDATE_LIMIT: usize = 10_000;

impl SpecLattice {
    /// Build the ε-neighborhood of `center` within the lattice.
    ///
    /// The procedure follows the prompt's algorithm: enumerate single-step
    /// neighbors (weakenings and strengthenings), keep those within Jaccard
    /// distance `epsilon` of `center`, then compute the partial order and
    /// its Hasse-reduced transitive reduction.  The empty spec and the
    /// `⊥` spec are always included so that the lattice has a least and a
    /// greatest element.
    pub fn build_local(
        signature: Signature,
        center: SpecElement,
        epsilon: f64,
        quantifier_rank: usize,
        model_bound: usize,
        entailment_checker: &dyn EntailmentChecker,
    ) -> Result<Self, LatticeConstructionError> {
        let metric = JaccardMetric::from_signature(&signature, model_bound);
        let center_axioms: Vec<Formula> = center.axioms.iter().cloned().collect();

        // Deduplicate by canonical key as we generate.
        let mut candidates: BTreeMap<Vec<u8>, SpecElement> = BTreeMap::new();
        candidates.insert(center.canonical_key.clone(), center.clone());

        // Weakenings: drop each axiom in turn.
        for a in &center.axioms {
            let mut next = center.axioms.clone();
            next.remove(a);
            let elem = SpecElement::new(next);
            if !candidates.contains_key(&elem.canonical_key) {
                let new_axioms: Vec<Formula> = elem.axioms.iter().cloned().collect();
                let d = metric.distance(&center_axioms, &new_axioms).distance;
                if d <= epsilon {
                    candidates.insert(elem.canonical_key.clone(), elem);
                }
            }
        }

        // Strengthenings: add each well-sorted atomic formula not already
        // entailed by the center.
        let atoms = enumerate_atomic_formulas(&signature);
        for p in atoms {
            if !entailment_checker.entails(&center_axioms, std::slice::from_ref(&p)) {
                let mut next = center.axioms.clone();
                next.insert(p.clone());
                let elem = SpecElement::new(next);
                if !candidates.contains_key(&elem.canonical_key) {
                    let new_axioms: Vec<Formula> = elem.axioms.iter().cloned().collect();
                    let d = metric.distance(&center_axioms, &new_axioms).distance;
                    if d <= epsilon {
                        candidates.insert(elem.canonical_key.clone(), elem);
                    }
                }
            }
        }

        // Always include the least and greatest elements so leq invariants
        // can be exercised.
        let bottom_elem = SpecElement::new(BTreeSet::new());
        candidates
            .entry(bottom_elem.canonical_key.clone())
            .or_insert(bottom_elem.clone());
        let mut top_axioms = BTreeSet::new();
        top_axioms.insert(Formula::Bot);
        let top_elem = SpecElement::new(top_axioms);
        candidates
            .entry(top_elem.canonical_key.clone())
            .or_insert(top_elem.clone());

        if candidates.len() > DEFAULT_CANDIDATE_LIMIT {
            eprintln!(
                "specmut: local lattice produced {} candidates before ε-filtering (limit {})",
                candidates.len(),
                DEFAULT_CANDIDATE_LIMIT
            );
        }

        let elements: Vec<SpecElement> = candidates.into_values().collect();
        let index: HashMap<Vec<u8>, usize> = elements
            .iter()
            .enumerate()
            .map(|(i, e)| (e.canonical_key.clone(), i))
            .collect();
        let bottom = index
            .get(bottom_elem.canonical_key())
            .copied()
            .expect("bottom inserted above");
        let top = index
            .get(top_elem.canonical_key())
            .copied()
            .expect("top inserted above");

        let n = elements.len();
        let mut leq_matrix = vec![vec![false; n]; n];
        let axiom_vecs: Vec<Vec<Formula>> = elements
            .iter()
            .map(|e| e.axioms.iter().cloned().collect())
            .collect();
        for i in 0..n {
            for j in 0..n {
                // i ≤ j  iff  j entails i.
                leq_matrix[i][j] = entailment_checker.entails(&axiom_vecs[j], &axiom_vecs[i]);
            }
        }

        let hasse = hasse_reduction(&leq_matrix);

        Ok(SpecLattice {
            signature,
            quantifier_rank,
            elements,
            leq_matrix,
            hasse,
            index,
            bottom,
            top,
        })
    }

    /// `a ≤ b` — true iff `b` entails `a`.
    pub fn leq(&self, a: usize, b: usize) -> bool {
        self.leq_matrix[a][b]
    }

    /// Index of the element whose axiom set is `a.axioms ∪ b.axioms`.
    ///
    /// Phase 2 limitation: the resulting element must already exist in the
    /// lattice.  This holds whenever one operand is `bottom` (the empty
    /// spec) or whenever a previous `build_local` pass produced the union;
    /// other cases panic.
    pub fn meet(&self, a: usize, b: usize) -> usize {
        let merged_axioms: BTreeSet<Formula> = self.elements[a]
            .axioms
            .union(&self.elements[b].axioms)
            .cloned()
            .collect();
        let merged = SpecElement::new(merged_axioms);
        match self.index.get(merged.canonical_key()) {
            Some(&idx) => idx,
            None => panic!(
                "meet({}, {}) not present in local lattice — extend build_local's neighborhood",
                a, b
            ),
        }
    }

    /// Index of the element whose axiom set is `a.axioms ∩ b.axioms`.
    ///
    /// As with [`Self::meet`], the result must already be in the lattice.
    pub fn join(&self, a: usize, b: usize) -> usize {
        let shared_axioms: BTreeSet<Formula> = self.elements[a]
            .axioms
            .intersection(&self.elements[b].axioms)
            .cloned()
            .collect();
        let joined = SpecElement::new(shared_axioms);
        match self.index.get(joined.canonical_key()) {
            Some(&idx) => idx,
            None => panic!(
                "join({}, {}) not present in local lattice — extend build_local's neighborhood",
                a, b
            ),
        }
    }

    /// The Hasse diagram of the local lattice: `hasse_diagram()[i]` is the
    /// list of indices that cover `i`.
    pub fn hasse_diagram(&self) -> &Vec<Vec<usize>> {
        &self.hasse
    }

    /// Index of the least element (the empty spec).
    pub fn bottom(&self) -> usize {
        self.bottom
    }

    /// Index of the greatest element (the inconsistent spec).
    pub fn top(&self) -> usize {
        self.top
    }

    /// Get a borrowed reference to an element by index.
    pub fn element(&self, idx: usize) -> &SpecElement {
        &self.elements[idx]
    }

    /// Number of elements in the lattice.
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// True iff the lattice is empty.  Always false after `build_local`
    /// (which always inserts at least bottom and top).
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Look up an element index by its canonical key, if present.
    pub fn index_of(&self, key: &[u8]) -> Option<usize> {
        self.index.get(key).copied()
    }

    /// Look up an element by its [`SpecElement`].  Added in Phase 4 for
    /// CEGIS lattice lookup: maps a mutant's spec back to its index in
    /// this lattice so that pruning can consult [`Self::leq`].
    pub fn find_element(&self, spec: &SpecElement) -> Option<usize> {
        self.index_of(spec.canonical_key())
    }

    /// The signature this lattice is built over.
    pub fn signature(&self) -> &Signature {
        &self.signature
    }

    /// The quantifier-rank bound supplied at construction time.
    pub fn quantifier_rank(&self) -> usize {
        self.quantifier_rank
    }

    /// Length of the longest chain in the lattice (in covering steps).
    pub fn height(&self) -> usize {
        let n = self.elements.len();
        if n == 0 {
            return 0;
        }
        let mut memo: Vec<Option<usize>> = vec![None; n];
        fn dfs(idx: usize, hasse: &[Vec<usize>], memo: &mut [Option<usize>]) -> usize {
            if let Some(v) = memo[idx] {
                return v;
            }
            let mut best = 0;
            for &next in &hasse[idx] {
                best = best.max(1 + dfs(next, hasse, memo));
            }
            memo[idx] = Some(best);
            best
        }
        (0..n).map(|i| dfs(i, &self.hasse, &mut memo)).max().unwrap_or(0)
    }

    /// Size of the largest antichain in the lattice.  Phase 2 uses a brute
    /// force enumeration of subsets when the lattice has at most 20
    /// elements; for larger lattices it falls back to a greedy lower bound.
    pub fn width(&self) -> usize {
        let n = self.elements.len();
        if n == 0 {
            return 0;
        }
        if n <= 20 {
            let mut best = 0;
            for mask in 0u32..(1u32 << n) {
                let indices: Vec<usize> = (0..n).filter(|i| (mask >> i) & 1 == 1).collect();
                if self.is_antichain(&indices) {
                    best = best.max(indices.len());
                }
            }
            best
        } else {
            // Greedy lower bound: count elements with no incoming or
            // outgoing covering edge — they are pairwise incomparable.
            let mut comparable_pairs = 0usize;
            for i in 0..n {
                for j in (i + 1)..n {
                    if self.leq_matrix[i][j] || self.leq_matrix[j][i] {
                        comparable_pairs += 1;
                    }
                }
            }
            let _ = comparable_pairs; // documentation: just a placeholder.
            // Simpler fallback: count the level with the most elements in
            // the Hasse diagram.
            let mut levels: BTreeMap<usize, usize> = BTreeMap::new();
            let mut depth: Vec<usize> = vec![0; n];
            // BFS from bottom assigning depth.
            let mut order: Vec<usize> = (0..n).collect();
            order.sort_by_key(|&i| -(self.leq_matrix[i].iter().filter(|b| **b).count() as isize));
            for &i in &order {
                let mut d = 0;
                for (j, dj) in depth.iter().enumerate() {
                    if j != i && self.leq_matrix[j][i] {
                        d = d.max(dj + 1);
                    }
                }
                depth[i] = d;
                *levels.entry(d).or_default() += 1;
            }
            levels.values().copied().max().unwrap_or(0)
        }
    }

    fn is_antichain(&self, indices: &[usize]) -> bool {
        for &i in indices {
            for &j in indices {
                if i != j && self.leq_matrix[i][j] {
                    return false;
                }
            }
        }
        true
    }
}

fn hasse_reduction(leq: &[Vec<bool>]) -> Vec<Vec<usize>> {
    let n = leq.len();
    let mut hasse = vec![Vec::new(); n];
    for i in 0..n {
        for j in 0..n {
            if i == j || !leq[i][j] {
                continue;
            }
            // i ≤ j strictly: skip the case where j ≤ i too (would mean
            // they are equivalent and ought to share an index, but we
            // tolerate it defensively).
            if leq[j][i] {
                continue;
            }
            let mut covered = true;
            for (k, leq_k) in leq.iter().enumerate() {
                if k == i || k == j {
                    continue;
                }
                if leq[i][k] && leq_k[j] && !leq[k][i] && !leq[j][k] {
                    covered = false;
                    break;
                }
            }
            if covered {
                hasse[i].push(j);
            }
        }
    }
    hasse
}

/// Apply structural canonicalization to a formula tree: reorder `And` /
/// `Or` children so the lexicographically smaller serialization appears on
/// the left.  Assumes the input is already in NNF.
fn canonicalize_tree(f: Formula) -> Formula {
    match f {
        Formula::And(l, r) => {
            let l = canonicalize_tree(*l);
            let r = canonicalize_tree(*r);
            let lb = SpecElement::canonical_serialize(&l);
            let rb = SpecElement::canonical_serialize(&r);
            if lb <= rb {
                Formula::And(Box::new(l), Box::new(r))
            } else {
                Formula::And(Box::new(r), Box::new(l))
            }
        }
        Formula::Or(l, r) => {
            let l = canonicalize_tree(*l);
            let r = canonicalize_tree(*r);
            let lb = SpecElement::canonical_serialize(&l);
            let rb = SpecElement::canonical_serialize(&r);
            if lb <= rb {
                Formula::Or(Box::new(l), Box::new(r))
            } else {
                Formula::Or(Box::new(r), Box::new(l))
            }
        }
        Formula::Forall { sort, body } => Formula::Forall {
            sort,
            body: Box::new(canonicalize_tree(*body)),
        },
        Formula::Exists { sort, body } => Formula::Exists {
            sort,
            body: Box::new(canonicalize_tree(*body)),
        },
        Formula::Not(inner) => Formula::Not(Box::new(canonicalize_tree(*inner))),
        other => other,
    }
}

fn serialize_formula(f: &Formula, out: &mut Vec<u8>) {
    match f {
        Formula::Top => out.push(0x00),
        Formula::Bot => out.push(0x01),
        Formula::Atom { relation, args } => {
            out.push(0x02);
            serialize_name(&relation.name, out);
            serialize_arg_count(args.len(), out);
            for a in args {
                serialize_term(a, out);
            }
        }
        Formula::NegAtom { relation, args } => {
            out.push(0x03);
            serialize_name(&relation.name, out);
            serialize_arg_count(args.len(), out);
            for a in args {
                serialize_term(a, out);
            }
        }
        Formula::Eq(a, b) => {
            out.push(0x04);
            serialize_term(a, out);
            serialize_term(b, out);
        }
        Formula::Neq(a, b) => {
            out.push(0x05);
            serialize_term(a, out);
            serialize_term(b, out);
        }
        Formula::And(l, r) => {
            let lb = SpecElement::canonical_serialize(l);
            let rb = SpecElement::canonical_serialize(r);
            out.push(0x06);
            if lb <= rb {
                out.extend_from_slice(&lb);
                out.extend_from_slice(&rb);
            } else {
                out.extend_from_slice(&rb);
                out.extend_from_slice(&lb);
            }
        }
        Formula::Or(l, r) => {
            let lb = SpecElement::canonical_serialize(l);
            let rb = SpecElement::canonical_serialize(r);
            out.push(0x07);
            if lb <= rb {
                out.extend_from_slice(&lb);
                out.extend_from_slice(&rb);
            } else {
                out.extend_from_slice(&rb);
                out.extend_from_slice(&lb);
            }
        }
        Formula::Forall { sort, body } => {
            out.push(0x08);
            serialize_name(&sort.name, out);
            serialize_formula(body, out);
        }
        Formula::Exists { sort, body } => {
            out.push(0x09);
            serialize_name(&sort.name, out);
            serialize_formula(body, out);
        }
        Formula::Not(inner) => {
            // §4.1 does not define a tag for `Not`; canonical formulas are
            // NNF and contain none.  Reserve 0x0A as a non-canonical
            // sentinel for completeness.
            out.push(0x0A);
            serialize_formula(inner, out);
        }
    }
}

fn serialize_term(t: &Term, out: &mut Vec<u8>) {
    match t {
        Term::Var(idx) => {
            out.push(0x10);
            let v = u32::try_from(*idx).unwrap_or(u32::MAX);
            out.extend_from_slice(&v.to_be_bytes());
        }
        Term::App { function, args } => {
            out.push(0x11);
            serialize_name(&function.name, out);
            serialize_arg_count(args.len(), out);
            for a in args {
                serialize_term(a, out);
            }
        }
    }
}

fn serialize_name(name: &str, out: &mut Vec<u8>) {
    out.extend_from_slice(name.as_bytes());
    out.push(0x00);
}

fn serialize_arg_count(n: usize, out: &mut Vec<u8>) {
    let v = u16::try_from(n).unwrap_or(u16::MAX);
    out.extend_from_slice(&v.to_be_bytes());
}

/// Enumerate the atomic-formula vocabulary used by the local lattice's
/// strengthening step (and reused by mutation generation).  For each
/// relation symbol we emit the fully-universally-quantified positive atom;
/// when constants exist for every domain sort, we also emit every ground
/// instance.  This is enough to make Phase 2 tests meaningful without
/// committing to a full quantifier-rank `k` enumeration.
pub(crate) fn enumerate_atomic_formulas(sig: &Signature) -> Vec<Formula> {
    let mut out = Vec::new();
    for r in &sig.relations {
        out.push(fully_quantified_atom(r));
        for ground in ground_instances(sig, r) {
            out.push(ground);
        }
    }
    out
}

fn fully_quantified_atom(r: &RelationSymbol) -> Formula {
    let args: Vec<Term> = (0..r.arity.len())
        .rev()
        .map(Term::Var)
        .collect();
    let mut body = Formula::Atom {
        relation: r.clone(),
        args,
    };
    for sort in r.arity.iter().rev() {
        body = Formula::Forall {
            sort: sort.clone(),
            body: Box::new(body),
        };
    }
    body
}

fn ground_instances(sig: &Signature, r: &RelationSymbol) -> Vec<Formula> {
    let mut by_sort: BTreeMap<SortSymbol, Vec<Term>> = BTreeMap::new();
    for c in &sig.constants {
        let term = Term::App {
            function: c.clone(),
            args: vec![],
        };
        by_sort.entry(c.codomain.clone()).or_default().push(term);
    }
    if r.arity.iter().any(|s| !by_sort.contains_key(s)) {
        return Vec::new();
    }
    let mut tuples: Vec<Vec<Term>> = vec![Vec::new()];
    for s in &r.arity {
        let candidates = by_sort.get(s).cloned().unwrap_or_default();
        let mut next = Vec::with_capacity(tuples.len() * candidates.len());
        for prefix in &tuples {
            for c in &candidates {
                let mut extended = prefix.clone();
                extended.push(c.clone());
                next.push(extended);
            }
        }
        tuples = next;
    }
    tuples
        .into_iter()
        .map(|args| Formula::Atom {
            relation: r.clone(),
            args,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::Term;
    use crate::model::ModelEnumerator;
    use crate::signature::{RelationSymbol, SortSymbol};

    fn sort(name: &str) -> SortSymbol {
        SortSymbol::new(name)
    }

    fn unary_sig() -> Signature {
        let s = sort("S");
        Signature::new(
            vec![s.clone()],
            vec![],
            vec![RelationSymbol::new("R", vec![s])],
        )
        .expect("valid sig")
    }

    fn r_atom(args: Vec<Term>) -> Formula {
        Formula::Atom {
            relation: RelationSymbol::new("R", vec![sort("S"); args.len()]),
            args,
        }
    }

    fn forall_r() -> Formula {
        Formula::Forall {
            sort: sort("S"),
            body: Box::new(r_atom(vec![Term::Var(0)])),
        }
    }

    fn pred(name: &str, var: usize) -> Formula {
        Formula::Atom {
            relation: RelationSymbol::new(name, vec![sort("S")]),
            args: vec![Term::Var(var)],
        }
    }

    #[test]
    fn canonical_key_is_deterministic_across_constructions() {
        let mut a1 = BTreeSet::new();
        a1.insert(pred("P", 0));
        a1.insert(pred("Q", 0));

        let mut a2 = BTreeSet::new();
        // Inserting in the opposite order should not matter — BTreeSet
        // already sorts — but we also verify the canonical-key bytes
        // match after canonicalization.
        a2.insert(pred("Q", 0));
        a2.insert(pred("P", 0));

        let e1 = SpecElement::new(a1);
        let e2 = SpecElement::new(a2);
        assert_eq!(e1.canonical_key(), e2.canonical_key());
        assert_eq!(e1, e2);
    }

    #[test]
    fn canonical_key_equates_swapped_conjuncts() {
        // (P ∧ Q) and (Q ∧ P) should serialize identically because the
        // serializer sorts `And` children.
        let p = pred("P", 0);
        let q = pred("Q", 0);
        let and1 = Formula::And(Box::new(p.clone()), Box::new(q.clone()));
        let and2 = Formula::And(Box::new(q), Box::new(p));
        let k1 = SpecElement::canonical_serialize(&and1);
        let k2 = SpecElement::canonical_serialize(&and2);
        assert_eq!(k1, k2);
    }

    #[test]
    fn canonical_serialize_top_and_bot_have_expected_tags() {
        assert_eq!(SpecElement::canonical_serialize(&Formula::Top), vec![0x00]);
        assert_eq!(SpecElement::canonical_serialize(&Formula::Bot), vec![0x01]);
    }

    #[test]
    fn model_entailment_checker_basic_cases() {
        let models: Vec<_> =
            ModelEnumerator::new(unary_sig(), 2).enumerate().collect();
        let checker = ModelEntailmentChecker::new(models);
        let q = forall_r();
        // {forall x.R(x)} entails itself trivially.
        assert!(checker.entails(std::slice::from_ref(&q), std::slice::from_ref(&q)));
        // Empty premise entails empty conclusion (trivially).
        assert!(checker.entails(&[], &[]));
        // {forall x.R(x)} entails {} (the tautology).
        assert!(checker.entails(std::slice::from_ref(&q), &[]));
        // {} does not entail {forall x.R(x)} — there are models where
        // forall fails.
        assert!(!checker.entails(&[], std::slice::from_ref(&q)));
    }

    #[test]
    fn model_entailment_independent_axioms_do_not_entail_each_other() {
        // Build a signature with two unary relations.
        let s = sort("S");
        let sig = Signature::new(
            vec![s.clone()],
            vec![],
            vec![
                RelationSymbol::new("P", vec![s.clone()]),
                RelationSymbol::new("Q", vec![s]),
            ],
        )
        .expect("valid");
        let models: Vec<_> = ModelEnumerator::new(sig, 2).enumerate().collect();
        let checker = ModelEntailmentChecker::new(models);
        let phi_p = Formula::Forall {
            sort: sort("S"),
            body: Box::new(pred("P", 0)),
        };
        let phi_q = Formula::Forall {
            sort: sort("S"),
            body: Box::new(pred("Q", 0)),
        };
        // P-axiom + Q-axiom entails P-axiom.
        assert!(checker.entails(&[phi_p.clone(), phi_q.clone()], std::slice::from_ref(&phi_p)));
        // P-axiom alone does not entail Q-axiom.
        assert!(!checker.entails(std::slice::from_ref(&phi_p), std::slice::from_ref(&phi_q)));
    }

    #[test]
    fn build_local_contains_center_and_bottom() {
        let sig = unary_sig();
        let models: Vec<_> =
            ModelEnumerator::new(sig.clone(), 2).enumerate().collect();
        let checker = ModelEntailmentChecker::new(models);
        let center = SpecElement::from_axioms([forall_r()]);
        let lattice = SpecLattice::build_local(sig, center.clone(), 1.0, 1, 2, &checker)
            .expect("build_local should succeed");
        assert!(lattice.index_of(center.canonical_key()).is_some());
        let empty = SpecElement::new(BTreeSet::new());
        assert_eq!(lattice.bottom(), lattice.index_of(empty.canonical_key()).expect("empty present"));
    }

    #[test]
    fn leq_bottom_to_any_is_true() {
        let sig = unary_sig();
        let models: Vec<_> =
            ModelEnumerator::new(sig.clone(), 2).enumerate().collect();
        let checker = ModelEntailmentChecker::new(models);
        let center = SpecElement::from_axioms([forall_r()]);
        let lattice = SpecLattice::build_local(sig, center, 1.0, 1, 2, &checker).expect("ok");
        let bottom = lattice.bottom();
        for x in 0..lattice.len() {
            assert!(
                lattice.leq(bottom, x),
                "leq(bottom, {x}) should be true; bottom is the least element"
            );
        }
    }

    #[test]
    fn meet_with_bottom_returns_other() {
        let sig = unary_sig();
        let models: Vec<_> =
            ModelEnumerator::new(sig.clone(), 2).enumerate().collect();
        let checker = ModelEntailmentChecker::new(models);
        let center = SpecElement::from_axioms([forall_r()]);
        let lattice = SpecLattice::build_local(sig, center.clone(), 1.0, 1, 2, &checker).expect("ok");
        let bottom = lattice.bottom();
        let center_idx = lattice.index_of(center.canonical_key()).expect("center");
        let met = lattice.meet(center_idx, bottom);
        // meet.axioms == center.axioms ∪ ∅ == center.axioms
        assert_eq!(lattice.element(met).axioms, lattice.element(center_idx).axioms);
    }

    #[test]
    fn hasse_diagram_height_bounded_by_chain_length() {
        let sig = unary_sig();
        let models: Vec<_> =
            ModelEnumerator::new(sig.clone(), 2).enumerate().collect();
        let checker = ModelEntailmentChecker::new(models);
        let center = SpecElement::from_axioms([forall_r()]);
        let lattice = SpecLattice::build_local(sig, center, 1.0, 1, 2, &checker).expect("ok");
        assert!(lattice.height() <= lattice.len());
    }
}
