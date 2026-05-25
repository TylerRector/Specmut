//! Parsers for specmut input formats.
//!
//! See §3.10 and §7 of the specification document.

pub mod dafny_parser;
pub mod fol_parser;
pub mod lean_elaborator;
pub mod lean_parser;

use specmut_core::formula::Formula;
use specmut_core::signature::Signature;
use thiserror::Error;

/// Trait shared by input-language parsers that produce a (signature, axioms)
/// pair suitable for the rest of the pipeline.
pub trait SpecParser {
    /// Parse `source` into a [`Signature`] and a list of axiom [`Formula`]s.
    fn parse(&self, source: &str) -> Result<(Signature, Vec<Formula>), ParseError>;
}

/// Errors raised by the parser layer.
#[derive(Debug, Error)]
pub enum ParseError {
    /// Lexical or grammatical error.  Line / column are 1-based and refer
    /// to the (post-comment-strip, post-Unicode-normalize) source.
    #[error("parse error at line {line}, col {col}: {message}")]
    Syntax {
        /// 1-based line number.
        line: usize,
        /// 1-based column number.
        col: usize,
        /// Human-readable description.
        message: String,
    },

    /// A function or relation arity referenced a sort that was not
    /// declared earlier in the file.
    #[error("undefined sort '{name}' referenced in {context}")]
    UndefinedSort {
        /// The missing sort.
        name: String,
        /// Where the reference appeared.
        context: String,
    },

    /// A function or relation symbol was used in an axiom without a
    /// corresponding declaration.
    #[error("undefined {symbol_kind} '{name}' used in axiom")]
    UndefinedSymbol {
        /// Either `"relation"` or `"function"`.
        symbol_kind: String,
        /// The missing symbol's name.
        name: String,
    },

    /// A symbol name was declared more than once across sorts /
    /// functions / relations.
    #[error("duplicate declaration of '{name}'")]
    Duplicate {
        /// The repeated name.
        name: String,
    },

    /// An axiom contained a free variable, i.e. an identifier that was
    /// not bound by an enclosing quantifier and was not a declared
    /// constant.
    #[error("expected sentence but formula has free variables: {formula}")]
    FreeVariables {
        /// Best-effort textual rendering of the offending formula or
        /// identifier.
        formula: String,
    },
}

impl From<specmut_core::signature::SignatureError> for ParseError {
    fn from(err: specmut_core::signature::SignatureError) -> Self {
        use specmut_core::signature::SignatureError as SE;
        match err {
            SE::DuplicateName(name) => ParseError::Duplicate { name },
            SE::UnknownSortInFunction { function, sort } => ParseError::UndefinedSort {
                name: sort,
                context: format!("function '{function}'"),
            },
            SE::UnknownSortInRelation { relation, sort } => ParseError::UndefinedSort {
                name: sort,
                context: format!("relation '{relation}'"),
            },
        }
    }
}
