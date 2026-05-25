//! First-order signatures Σ.
//!
//! A signature is the vocabulary over which specifications are written: a set
//! of sorts, a set of function symbols (each typed by a domain and codomain),
//! and a set of relation symbols (each typed by an arity tuple).
//!
//! See §3.1 of the specification document.

use std::collections::BTreeSet;

use num_bigint::BigUint;
use thiserror::Error;

/// A sort (type) in the signature.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SortSymbol {
    /// The textual name of the sort.
    pub name: String,
}

impl SortSymbol {
    /// Build a sort from anything that can be turned into a [`String`].
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }
}

/// A function symbol with its arity (domain sorts → codomain sort).
///
/// A function symbol with an empty `domain` is a constant.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunctionSymbol {
    /// The textual name of the function.
    pub name: String,
    /// The list of domain sorts, in order.
    pub domain: Vec<SortSymbol>,
    /// The codomain sort.
    pub codomain: SortSymbol,
}

impl FunctionSymbol {
    /// Build a function symbol.
    pub fn new(
        name: impl Into<String>,
        domain: Vec<SortSymbol>,
        codomain: SortSymbol,
    ) -> Self {
        Self {
            name: name.into(),
            domain,
            codomain,
        }
    }

    /// True iff this is a 0-ary function (a constant).
    pub fn is_constant(&self) -> bool {
        self.domain.is_empty()
    }
}

/// A relation symbol with its arity.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RelationSymbol {
    /// The textual name of the relation.
    pub name: String,
    /// The list of sorts the relation relates, in order.
    pub arity: Vec<SortSymbol>,
}

impl RelationSymbol {
    /// Build a relation symbol.
    pub fn new(name: impl Into<String>, arity: Vec<SortSymbol>) -> Self {
        Self {
            name: name.into(),
            arity,
        }
    }
}

/// A first-order signature Σ.
///
/// INVARIANT: No duplicate names across sorts, functions, and relations.
/// INVARIANT: All sorts referenced in function/relation arities exist in
/// `sorts`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Signature {
    /// The set of sorts.
    pub sorts: BTreeSet<SortSymbol>,
    /// The set of function symbols.
    pub functions: BTreeSet<FunctionSymbol>,
    /// The set of relation symbols.
    pub relations: BTreeSet<RelationSymbol>,
    /// The subset of `functions` consisting of constants (empty domain).
    pub constants: BTreeSet<FunctionSymbol>,
}

/// Errors that can arise when constructing a [`Signature`].
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum SignatureError {
    /// A name appears more than once across sorts, functions, and relations.
    #[error("duplicate symbol name: '{0}'")]
    DuplicateName(String),

    /// A function symbol references a sort that is not declared in `sorts`.
    #[error("function '{function}' references unknown sort '{sort}'")]
    UnknownSortInFunction {
        /// Name of the offending function.
        function: String,
        /// Name of the missing sort.
        sort: String,
    },

    /// A relation symbol references a sort that is not declared in `sorts`.
    #[error("relation '{relation}' references unknown sort '{sort}'")]
    UnknownSortInRelation {
        /// Name of the offending relation.
        relation: String,
        /// Name of the missing sort.
        sort: String,
    },
}

impl Signature {
    /// Construct a new signature, validating its invariants.
    ///
    /// Returns [`SignatureError::DuplicateName`] if a name is shared across
    /// sorts, functions, and relations, or [`SignatureError::UnknownSortInFunction`]
    /// / [`SignatureError::UnknownSortInRelation`] for dangling sort
    /// references.
    pub fn new(
        sorts: Vec<SortSymbol>,
        functions: Vec<FunctionSymbol>,
        relations: Vec<RelationSymbol>,
    ) -> Result<Self, SignatureError> {
        let mut seen: BTreeSet<String> = BTreeSet::new();
        for s in &sorts {
            if !seen.insert(s.name.clone()) {
                return Err(SignatureError::DuplicateName(s.name.clone()));
            }
        }
        for f in &functions {
            if !seen.insert(f.name.clone()) {
                return Err(SignatureError::DuplicateName(f.name.clone()));
            }
        }
        for r in &relations {
            if !seen.insert(r.name.clone()) {
                return Err(SignatureError::DuplicateName(r.name.clone()));
            }
        }

        let sort_set: BTreeSet<SortSymbol> = sorts.iter().cloned().collect();

        for f in &functions {
            for s in f.domain.iter().chain(std::iter::once(&f.codomain)) {
                if !sort_set.contains(s) {
                    return Err(SignatureError::UnknownSortInFunction {
                        function: f.name.clone(),
                        sort: s.name.clone(),
                    });
                }
            }
        }
        for r in &relations {
            for s in &r.arity {
                if !sort_set.contains(s) {
                    return Err(SignatureError::UnknownSortInRelation {
                        relation: r.name.clone(),
                        sort: s.name.clone(),
                    });
                }
            }
        }

        let constants: BTreeSet<FunctionSymbol> = functions
            .iter()
            .filter(|f| f.is_constant())
            .cloned()
            .collect();

        Ok(Self {
            sorts: sort_set,
            functions: functions.into_iter().collect(),
            relations: relations.into_iter().collect(),
            constants,
        })
    }

    /// The number of distinct *relation* interpretations over a domain of
    /// size `n`. For relation symbols of arities a₁, …, aₖ this equals
    /// ∏ᵢ 2^(n^aᵢ). Function interpretations are not included; see §3.1.
    pub fn model_space_size(&self, domain_size: usize) -> BigUint {
        let n = BigUint::from(domain_size);
        let two = BigUint::from(2u32);
        let mut total = BigUint::from(1u32);
        for r in &self.relations {
            let arity = u32::try_from(r.arity.len()).unwrap_or(u32::MAX);
            let tuples: BigUint = n.pow(arity);
            let exponent = u32::try_from(&tuples).unwrap_or(u32::MAX);
            total *= two.pow(exponent);
        }
        total
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(name: &str) -> SortSymbol {
        SortSymbol::new(name)
    }

    #[test]
    fn valid_signature_constructs() {
        let elem = s("Elem");
        let seq = s("Seq");
        let sig = Signature::new(
            vec![elem.clone(), seq.clone()],
            vec![FunctionSymbol::new(
                "output",
                vec![seq.clone()],
                seq.clone(),
            )],
            vec![
                RelationSymbol::new("leq", vec![elem.clone(), elem.clone()]),
                RelationSymbol::new("sorted", vec![seq.clone()]),
            ],
        )
        .expect("signature construction should succeed");
        assert_eq!(sig.sorts.len(), 2);
        assert_eq!(sig.functions.len(), 1);
        assert_eq!(sig.relations.len(), 2);
        assert!(sig.constants.is_empty());
    }

    #[test]
    fn duplicate_sort_name_is_error() {
        let err = Signature::new(vec![s("A"), s("A")], vec![], vec![])
            .expect_err("duplicate sort name should error");
        assert_eq!(err, SignatureError::DuplicateName("A".into()));
    }

    #[test]
    fn duplicate_across_kinds_is_error() {
        let err = Signature::new(
            vec![s("X")],
            vec![FunctionSymbol::new("X", vec![], s("X"))],
            vec![],
        )
        .expect_err("name shared across sort + function should error");
        assert_eq!(err, SignatureError::DuplicateName("X".into()));
    }

    #[test]
    fn dangling_sort_in_function_is_error() {
        let err = Signature::new(
            vec![s("A")],
            vec![FunctionSymbol::new("f", vec![s("A")], s("B"))],
            vec![],
        )
        .expect_err("undeclared codomain sort should error");
        assert_eq!(
            err,
            SignatureError::UnknownSortInFunction {
                function: "f".into(),
                sort: "B".into(),
            }
        );
    }

    #[test]
    fn dangling_sort_in_relation_is_error() {
        let err = Signature::new(
            vec![s("A")],
            vec![],
            vec![RelationSymbol::new("R", vec![s("Z")])],
        )
        .expect_err("undeclared arity sort should error");
        assert_eq!(
            err,
            SignatureError::UnknownSortInRelation {
                relation: "R".into(),
                sort: "Z".into(),
            }
        );
    }

    #[test]
    fn constants_extracted() {
        let a = s("A");
        let sig = Signature::new(
            vec![a.clone()],
            vec![
                FunctionSymbol::new("c", vec![], a.clone()),
                FunctionSymbol::new("f", vec![a.clone()], a.clone()),
            ],
            vec![],
        )
        .expect("ok");
        assert_eq!(sig.constants.len(), 1);
        assert!(sig.constants.iter().any(|f| f.name == "c"));
    }

    #[test]
    fn model_space_size_two_binary_relations_domain_three() {
        let a = s("A");
        let sig = Signature::new(
            vec![a.clone()],
            vec![],
            vec![
                RelationSymbol::new("R", vec![a.clone(), a.clone()]),
                RelationSymbol::new("S", vec![a.clone(), a.clone()]),
            ],
        )
        .expect("ok");
        // 2^(3^2) * 2^(3^2) = 2^9 * 2^9 = 2^18
        let expected = BigUint::from(2u32).pow(18);
        assert_eq!(sig.model_space_size(3), expected);
    }

    #[test]
    fn model_space_size_no_relations_is_one() {
        let sig = Signature::new(vec![s("A")], vec![], vec![]).expect("ok");
        assert_eq!(sig.model_space_size(5), BigUint::from(1u32));
    }
}
