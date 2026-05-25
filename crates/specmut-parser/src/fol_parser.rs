//! FOL parser — the canonical input format defined in §7.1.
//!
//! The pipeline is:
//!
//! 1. Strip comments (`-- line` and `{- block -}`) and normalize Unicode
//!    aliases (`∀ → forall`, `∧ → /\`, etc.).
//! 2. Run the nom-based parser against the preprocessed source to obtain
//!    a [`RawSpec`] (intermediate AST with named variables).
//! 3. Validate declarations and build a [`Signature`].
//! 4. Desugar `→` / `↔` into NNF building blocks, convert named
//!    variables to de Bruijn indices, and apply [`Formula::to_nnf`].
//! 5. Reject any axiom that is not a sentence.

use std::collections::HashMap;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, multispace0, multispace1},
    combinator::{map, recognize},
    multi::{many0, separated_list0, separated_list1},
    sequence::{delimited, pair},
    IResult,
};

use specmut_core::formula::{Formula, Term};
use specmut_core::signature::{FunctionSymbol, RelationSymbol, Signature, SortSymbol};

use crate::{ParseError, SpecParser};

/// FOL parser implementing [`SpecParser`].
#[derive(Debug, Default, Clone, Copy)]
pub struct FolParser;

impl SpecParser for FolParser {
    fn parse(&self, source: &str) -> Result<(Signature, Vec<Formula>), ParseError> {
        parse_fol(source)
    }
}

/// Top-level entry point.
pub fn parse_fol(source: &str) -> Result<(Signature, Vec<Formula>), ParseError> {
    let preprocessed = strip_comments(&normalize_unicode(source));
    let (rest, raw_spec) = parse_spec(&preprocessed).map_err(|e| match e {
        nom::Err::Incomplete(_) => ParseError::Syntax {
            line: 1,
            col: 1,
            message: "unexpected end of input".to_string(),
        },
        nom::Err::Error(err) | nom::Err::Failure(err) => locate_error(&preprocessed, err.input),
    })?;
    if !rest.trim().is_empty() {
        return Err(locate_error(&preprocessed, rest));
    }

    let signature = build_signature(&raw_spec)?;

    let mut formulas = Vec::with_capacity(raw_spec.axioms.len());
    for raw in raw_spec.axioms {
        let desugared = desugar(raw);
        let f = to_de_bruijn(desugared, &mut Vec::new(), &signature)?;
        let nnf = Formula::to_nnf(f);
        if !nnf.is_sentence() {
            return Err(ParseError::FreeVariables {
                formula: format_formula(&nnf),
            });
        }
        formulas.push(nnf);
    }

    Ok((signature, formulas))
}

// ---------- Preprocessing ----------

fn normalize_unicode(source: &str) -> String {
    source
        .replace('∀', "forall")
        .replace('∃', "exists")
        .replace('∧', "/\\")
        .replace('∨', "\\/")
        .replace('¬', "~")
        .replace('↔', "<->")
        .replace('→', "->")
}

/// Strip comments while preserving line/column positions for downstream
/// error reports.  Both `--` line comments and `{- ... -}` block comments
/// are replaced with whitespace of equal width; newlines inside block
/// comments are preserved so line counts stay aligned.
fn strip_comments(source: &str) -> String {
    let mut out = String::with_capacity(source.len());
    let mut chars = source.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '-' && chars.peek() == Some(&'-') {
            // Line comment.
            out.push(' ');
            chars.next();
            out.push(' ');
            while let Some(&nx) = chars.peek() {
                if nx == '\n' {
                    break;
                }
                chars.next();
                out.push(if nx.is_whitespace() { nx } else { ' ' });
            }
        } else if c == '{' && chars.peek() == Some(&'-') {
            // Block comment.
            out.push(' ');
            chars.next();
            out.push(' ');
            let mut prev = '\0';
            for nx in chars.by_ref() {
                out.push(if nx == '\n' {
                    '\n'
                } else if nx.is_whitespace() {
                    nx
                } else {
                    ' '
                });
                if prev == '-' && nx == '}' {
                    break;
                }
                prev = nx;
            }
        } else {
            out.push(c);
        }
    }
    out
}

fn locate_error(source: &str, remaining: &str) -> ParseError {
    let consumed = source.len().saturating_sub(remaining.len());
    let mut line = 1usize;
    let mut col = 1usize;
    for c in source.chars().take(consumed) {
        if c == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    let preview: String = remaining.chars().take(20).collect();
    ParseError::Syntax {
        line,
        col,
        message: format!("unexpected input near '{preview}'"),
    }
}

// ---------- Raw AST ----------

#[derive(Debug)]
struct RawSpec {
    declarations: Vec<RawDecl>,
    axioms: Vec<RawFormula>,
}

#[derive(Debug)]
enum RawDecl {
    Sort(String),
    Func {
        name: String,
        domain: Vec<String>,
        codomain: String,
    },
    Rel {
        name: String,
        arity: Vec<String>,
    },
    Const {
        name: String,
        sort: String,
    },
}

#[derive(Debug, Clone)]
enum RawTerm {
    NamedVar(String),
    App { function: String, args: Vec<RawTerm> },
}

#[derive(Debug, Clone)]
enum RawFormula {
    Top,
    Bot,
    Atom {
        relation: String,
        args: Vec<RawTerm>,
    },
    Eq(RawTerm, RawTerm),
    Neq(RawTerm, RawTerm),
    Not(Box<RawFormula>),
    And(Box<RawFormula>, Box<RawFormula>),
    Or(Box<RawFormula>, Box<RawFormula>),
    Implies(Box<RawFormula>, Box<RawFormula>),
    Iff(Box<RawFormula>, Box<RawFormula>),
    Forall {
        var: String,
        sort: String,
        body: Box<RawFormula>,
    },
    Exists {
        var: String,
        sort: String,
        body: Box<RawFormula>,
    },
}

// ---------- nom parsers ----------

const KEYWORDS: &[&str] = &[
    "sort", "func", "rel", "const", "axiom", "forall", "exists", "true", "false",
];

fn keyword<'a>(input: &'a str, kw: &str) -> IResult<&'a str, ()> {
    if !input.starts_with(kw) {
        return Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Tag,
        )));
    }
    let rest = &input[kw.len()..];
    if rest
        .chars()
        .next()
        .is_none_or(|c| !c.is_alphanumeric() && c != '_')
    {
        Ok((rest, ()))
    } else {
        Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Tag,
        )))
    }
}

fn ident(input: &str) -> IResult<&str, &str> {
    let (rest, name) = recognize(pair(
        alt((alpha1, tag("_"))),
        many0(alt((alphanumeric1, tag("_")))),
    ))(input)?;
    if KEYWORDS.contains(&name) {
        Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Tag,
        )))
    } else {
        Ok((rest, name))
    }
}

fn ident_owned(input: &str) -> IResult<&str, String> {
    map(ident, |s: &str| s.to_string())(input)
}

fn ws_comma(input: &str) -> IResult<&str, &str> {
    delimited(multispace0, tag(","), multispace0)(input)
}

fn parse_spec(input: &str) -> IResult<&str, RawSpec> {
    let (input, _) = multispace0(input)?;
    let mut declarations = Vec::new();
    let mut input = input;
    // Decls can be interleaved with axioms; per the grammar, decls precede
    // axioms, but in practice we accept either order until we hit
    // something that parses as an axiom.
    loop {
        let after_ws = multispace0::<_, nom::error::Error<&str>>(input)
            .map(|(rest, _)| rest)
            .unwrap_or(input);
        if let Ok((rest, decl_value)) = decl(after_ws) {
            declarations.push(decl_value);
            input = rest;
            continue;
        }
        break;
    }
    let (input, _) = multispace0(input)?;
    let mut axioms = Vec::new();
    let mut input = input;
    loop {
        let rest = multispace0::<_, nom::error::Error<&str>>(input)
            .map(|(rest, _)| rest)
            .unwrap_or(input);
        if rest.is_empty() {
            input = rest;
            break;
        }
        match axiom(rest) {
            Ok((rest2, ax)) => {
                axioms.push(ax);
                input = rest2;
            }
            Err(e) => {
                return Err(e);
            }
        }
    }
    Ok((
        input,
        RawSpec {
            declarations,
            axioms,
        },
    ))
}

fn decl(input: &str) -> IResult<&str, RawDecl> {
    alt((sort_decl, func_decl, rel_decl, const_decl))(input)
}

fn sort_decl(input: &str) -> IResult<&str, RawDecl> {
    let (input, _) = keyword(input, "sort")?;
    let (input, _) = multispace1(input)?;
    let (input, name) = ident(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(".")(input)?;
    Ok((input, RawDecl::Sort(name.to_string())))
}

fn func_decl(input: &str) -> IResult<&str, RawDecl> {
    let (input, _) = keyword(input, "func")?;
    let (input, _) = multispace1(input)?;
    let (input, name) = ident(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(":")(input)?;
    let (input, _) = multispace0(input)?;
    let (input, domain) = separated_list1(ws_comma, ident_owned)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("->")(input)?;
    let (input, _) = multispace0(input)?;
    let (input, codomain) = ident(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(".")(input)?;
    Ok((
        input,
        RawDecl::Func {
            name: name.to_string(),
            domain,
            codomain: codomain.to_string(),
        },
    ))
}

fn rel_decl(input: &str) -> IResult<&str, RawDecl> {
    let (input, _) = keyword(input, "rel")?;
    let (input, _) = multispace1(input)?;
    let (input, name) = ident(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(":")(input)?;
    let (input, _) = multispace0(input)?;
    let (input, arity) = separated_list1(ws_comma, ident_owned)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(".")(input)?;
    Ok((
        input,
        RawDecl::Rel {
            name: name.to_string(),
            arity,
        },
    ))
}

fn const_decl(input: &str) -> IResult<&str, RawDecl> {
    let (input, _) = keyword(input, "const")?;
    let (input, _) = multispace1(input)?;
    let (input, name) = ident(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(":")(input)?;
    let (input, _) = multispace0(input)?;
    let (input, sort) = ident(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(".")(input)?;
    Ok((
        input,
        RawDecl::Const {
            name: name.to_string(),
            sort: sort.to_string(),
        },
    ))
}

fn axiom(input: &str) -> IResult<&str, RawFormula> {
    let (input, _) = keyword(input, "axiom")?;
    let (input, _) = multispace1(input)?;
    let (input, f) = formula(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(".")(input)?;
    Ok((input, f))
}

fn formula(input: &str) -> IResult<&str, RawFormula> {
    biconditional(input)
}

fn biconditional(input: &str) -> IResult<&str, RawFormula> {
    let (input, left) = implication(input)?;
    let (after_ws, _) = multispace0(input)?;
    if let Ok((rest, _)) = tag::<_, _, nom::error::Error<&str>>("<->")(after_ws) {
        let (rest, _) = multispace0(rest)?;
        let (rest, right) = biconditional(rest)?;
        return Ok((rest, RawFormula::Iff(Box::new(left), Box::new(right))));
    }
    Ok((input, left))
}

fn implication(input: &str) -> IResult<&str, RawFormula> {
    let (input, left) = disjunction(input)?;
    let (after_ws, _) = multispace0(input)?;
    // "->" must not be the prefix of "<->" — but biconditional was tried
    // already at the outer level, so seeing "->" here means implication.
    if after_ws.starts_with("->") && !after_ws.starts_with("->>") {
        let rest = &after_ws[2..];
        let (rest, _) = multispace0(rest)?;
        let (rest, right) = implication(rest)?;
        return Ok((rest, RawFormula::Implies(Box::new(left), Box::new(right))));
    }
    Ok((input, left))
}

fn disjunction(input: &str) -> IResult<&str, RawFormula> {
    let (input, left) = conjunction(input)?;
    let (after_ws, _) = multispace0(input)?;
    if let Ok((rest, _)) = tag::<_, _, nom::error::Error<&str>>("\\/")(after_ws) {
        let (rest, _) = multispace0(rest)?;
        let (rest, right) = disjunction(rest)?;
        return Ok((rest, RawFormula::Or(Box::new(left), Box::new(right))));
    }
    Ok((input, left))
}

fn conjunction(input: &str) -> IResult<&str, RawFormula> {
    let (input, left) = negation(input)?;
    let (after_ws, _) = multispace0(input)?;
    if let Ok((rest, _)) = tag::<_, _, nom::error::Error<&str>>("/\\")(after_ws) {
        let (rest, _) = multispace0(rest)?;
        let (rest, right) = conjunction(rest)?;
        return Ok((rest, RawFormula::And(Box::new(left), Box::new(right))));
    }
    Ok((input, left))
}

fn negation(input: &str) -> IResult<&str, RawFormula> {
    let (input, _) = multispace0(input)?;
    if let Ok((rest, _)) = tag::<_, _, nom::error::Error<&str>>("~")(input) {
        let (rest, _) = multispace0(rest)?;
        let (rest, inner) = negation(rest)?;
        return Ok((rest, RawFormula::Not(Box::new(inner))));
    }
    primary(input)
}

fn primary(input: &str) -> IResult<&str, RawFormula> {
    let (input, _) = multispace0(input)?;
    alt((
        |i| {
            let (i, _) = keyword(i, "true")?;
            Ok((i, RawFormula::Top))
        },
        |i| {
            let (i, _) = keyword(i, "false")?;
            Ok((i, RawFormula::Bot))
        },
        quantifier,
        parens,
        atomic,
    ))(input)
}

fn parens(input: &str) -> IResult<&str, RawFormula> {
    let (input, _) = tag("(")(input)?;
    let (input, _) = multispace0(input)?;
    let (input, f) = formula(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(")")(input)?;
    Ok((input, f))
}

fn quantifier(input: &str) -> IResult<&str, RawFormula> {
    let (input, is_forall) = alt((
        map(|i| keyword(i, "forall"), |_| true),
        map(|i| keyword(i, "exists"), |_| false),
    ))(input)?;
    let (input, _) = multispace1(input)?;
    let (input, var) = ident(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(":")(input)?;
    let (input, _) = multispace0(input)?;
    let (input, sort) = ident(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(".")(input)?;
    let (input, _) = multispace0(input)?;
    let (input, body) = formula(input)?;
    let f = if is_forall {
        RawFormula::Forall {
            var: var.to_string(),
            sort: sort.to_string(),
            body: Box::new(body),
        }
    } else {
        RawFormula::Exists {
            var: var.to_string(),
            sort: sort.to_string(),
            body: Box::new(body),
        }
    };
    Ok((input, f))
}

fn atomic(input: &str) -> IResult<&str, RawFormula> {
    alt((eq_or_neq, relation_app))(input)
}

fn eq_or_neq(input: &str) -> IResult<&str, RawFormula> {
    let (input, lhs) = term(input)?;
    let (input, _) = multispace0(input)?;
    let (input, op) = alt((tag("!="), tag("=")))(input)?;
    let (input, _) = multispace0(input)?;
    let (input, rhs) = term(input)?;
    let f = if op == "!=" {
        RawFormula::Neq(lhs, rhs)
    } else {
        RawFormula::Eq(lhs, rhs)
    };
    Ok((input, f))
}

fn relation_app(input: &str) -> IResult<&str, RawFormula> {
    let (input, name) = ident(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, _) = multispace0(input)?;
    let (input, args) = separated_list0(ws_comma, term)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(")")(input)?;
    Ok((
        input,
        RawFormula::Atom {
            relation: name.to_string(),
            args,
        },
    ))
}

fn term(input: &str) -> IResult<&str, RawTerm> {
    let (input, _) = multispace0(input)?;
    let (input, name) = ident(input)?;
    let after_name = input;
    let (input, _) = multispace0(input)?;
    if let Ok((rest, _)) = tag::<_, _, nom::error::Error<&str>>("(")(input) {
        let (rest, _) = multispace0(rest)?;
        let (rest, args) = separated_list0(ws_comma, term)(rest)?;
        let (rest, _) = multispace0(rest)?;
        let (rest, _) = tag(")")(rest)?;
        Ok((
            rest,
            RawTerm::App {
                function: name.to_string(),
                args,
            },
        ))
    } else {
        // No parens — bare identifier.  Return position before the
        // attempted whitespace skip so trailing space isn't consumed.
        Ok((after_name, RawTerm::NamedVar(name.to_string())))
    }
}

// ---------- Signature construction ----------

fn build_signature(raw: &RawSpec) -> Result<Signature, ParseError> {
    let mut sorts = Vec::new();
    let mut functions = Vec::new();
    let mut relations = Vec::new();
    let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for decl in &raw.declarations {
        match decl {
            RawDecl::Sort(name) => {
                if !seen.insert(name.clone()) {
                    return Err(ParseError::Duplicate { name: name.clone() });
                }
                sorts.push(SortSymbol::new(name));
            }
            RawDecl::Func {
                name,
                domain,
                codomain,
            } => {
                if !seen.insert(name.clone()) {
                    return Err(ParseError::Duplicate { name: name.clone() });
                }
                let dom: Vec<SortSymbol> =
                    domain.iter().map(SortSymbol::new).collect();
                functions.push(FunctionSymbol::new(name, dom, SortSymbol::new(codomain)));
            }
            RawDecl::Rel { name, arity } => {
                if !seen.insert(name.clone()) {
                    return Err(ParseError::Duplicate { name: name.clone() });
                }
                let arity_syms: Vec<SortSymbol> =
                    arity.iter().map(SortSymbol::new).collect();
                relations.push(RelationSymbol::new(name, arity_syms));
            }
            RawDecl::Const { name, sort } => {
                if !seen.insert(name.clone()) {
                    return Err(ParseError::Duplicate { name: name.clone() });
                }
                functions.push(FunctionSymbol::new(name, vec![], SortSymbol::new(sort)));
            }
        }
    }
    Ok(Signature::new(sorts, functions, relations)?)
}

// ---------- Desugar + de Bruijn + NNF ----------

fn desugar(raw: RawFormula) -> RawFormula {
    match raw {
        RawFormula::Top | RawFormula::Bot => raw,
        RawFormula::Atom { .. } | RawFormula::Eq(_, _) | RawFormula::Neq(_, _) => raw,
        RawFormula::Not(inner) => RawFormula::Not(Box::new(desugar(*inner))),
        RawFormula::And(l, r) => {
            RawFormula::And(Box::new(desugar(*l)), Box::new(desugar(*r)))
        }
        RawFormula::Or(l, r) => RawFormula::Or(Box::new(desugar(*l)), Box::new(desugar(*r))),
        RawFormula::Implies(a, b) => {
            let a = desugar(*a);
            let b = desugar(*b);
            RawFormula::Or(Box::new(RawFormula::Not(Box::new(a))), Box::new(b))
        }
        RawFormula::Iff(a, b) => {
            let a = desugar(*a);
            let b = desugar(*b);
            let a_to_b = RawFormula::Or(
                Box::new(RawFormula::Not(Box::new(a.clone()))),
                Box::new(b.clone()),
            );
            let b_to_a = RawFormula::Or(
                Box::new(RawFormula::Not(Box::new(b))),
                Box::new(a),
            );
            RawFormula::And(Box::new(a_to_b), Box::new(b_to_a))
        }
        RawFormula::Forall { var, sort, body } => RawFormula::Forall {
            var,
            sort,
            body: Box::new(desugar(*body)),
        },
        RawFormula::Exists { var, sort, body } => RawFormula::Exists {
            var,
            sort,
            body: Box::new(desugar(*body)),
        },
    }
}

fn to_de_bruijn(
    raw: RawFormula,
    env: &mut Vec<String>,
    sig: &Signature,
) -> Result<Formula, ParseError> {
    let constant_map = build_constant_map(sig);
    let function_map = build_function_map(sig);
    let relation_map = build_relation_map(sig);
    to_db_inner(raw, env, sig, &constant_map, &function_map, &relation_map)
}

fn to_db_inner(
    raw: RawFormula,
    env: &mut Vec<String>,
    sig: &Signature,
    constants: &HashMap<String, FunctionSymbol>,
    functions: &HashMap<String, FunctionSymbol>,
    relations: &HashMap<String, RelationSymbol>,
) -> Result<Formula, ParseError> {
    match raw {
        RawFormula::Top => Ok(Formula::Top),
        RawFormula::Bot => Ok(Formula::Bot),
        RawFormula::Atom { relation, args } => {
            let rel_sym = relations
                .get(&relation)
                .cloned()
                .ok_or_else(|| ParseError::UndefinedSymbol {
                    symbol_kind: "relation".to_string(),
                    name: relation.clone(),
                })?;
            let translated: Result<Vec<Term>, ParseError> = args
                .into_iter()
                .map(|t| term_to_de_bruijn(t, env, constants, functions))
                .collect();
            Ok(Formula::Atom {
                relation: rel_sym,
                args: translated?,
            })
        }
        RawFormula::Eq(a, b) => {
            let a = term_to_de_bruijn(a, env, constants, functions)?;
            let b = term_to_de_bruijn(b, env, constants, functions)?;
            Ok(Formula::Eq(a, b))
        }
        RawFormula::Neq(a, b) => {
            let a = term_to_de_bruijn(a, env, constants, functions)?;
            let b = term_to_de_bruijn(b, env, constants, functions)?;
            Ok(Formula::Neq(a, b))
        }
        RawFormula::Not(inner) => Ok(Formula::Not(Box::new(to_db_inner(
            *inner, env, sig, constants, functions, relations,
        )?))),
        RawFormula::And(l, r) => Ok(Formula::And(
            Box::new(to_db_inner(*l, env, sig, constants, functions, relations)?),
            Box::new(to_db_inner(*r, env, sig, constants, functions, relations)?),
        )),
        RawFormula::Or(l, r) => Ok(Formula::Or(
            Box::new(to_db_inner(*l, env, sig, constants, functions, relations)?),
            Box::new(to_db_inner(*r, env, sig, constants, functions, relations)?),
        )),
        RawFormula::Implies(_, _) | RawFormula::Iff(_, _) => unreachable!(
            "Implies/Iff should have been desugared before to_de_bruijn"
        ),
        RawFormula::Forall { var, sort, body } => {
            let sort_sym = SortSymbol::new(&sort);
            if !sig.sorts.contains(&sort_sym) {
                return Err(ParseError::UndefinedSort {
                    name: sort,
                    context: format!("forall binder '{var}'"),
                });
            }
            env.push(var);
            let body = to_db_inner(*body, env, sig, constants, functions, relations)?;
            env.pop();
            Ok(Formula::Forall {
                sort: sort_sym,
                body: Box::new(body),
            })
        }
        RawFormula::Exists { var, sort, body } => {
            let sort_sym = SortSymbol::new(&sort);
            if !sig.sorts.contains(&sort_sym) {
                return Err(ParseError::UndefinedSort {
                    name: sort,
                    context: format!("exists binder '{var}'"),
                });
            }
            env.push(var);
            let body = to_db_inner(*body, env, sig, constants, functions, relations)?;
            env.pop();
            Ok(Formula::Exists {
                sort: sort_sym,
                body: Box::new(body),
            })
        }
    }
}

fn term_to_de_bruijn(
    raw: RawTerm,
    env: &[String],
    constants: &HashMap<String, FunctionSymbol>,
    functions: &HashMap<String, FunctionSymbol>,
) -> Result<Term, ParseError> {
    match raw {
        RawTerm::NamedVar(name) => {
            if let Some(pos) = env.iter().rposition(|n| n == &name) {
                Ok(Term::Var(env.len() - 1 - pos))
            } else if let Some(c) = constants.get(&name).cloned() {
                Ok(Term::App {
                    function: c,
                    args: vec![],
                })
            } else {
                Err(ParseError::FreeVariables { formula: name })
            }
        }
        RawTerm::App { function, args } => {
            let fun_sym =
                functions
                    .get(&function)
                    .cloned()
                    .ok_or_else(|| ParseError::UndefinedSymbol {
                        symbol_kind: "function".to_string(),
                        name: function.clone(),
                    })?;
            let translated: Result<Vec<Term>, ParseError> = args
                .into_iter()
                .map(|t| term_to_de_bruijn(t, env, constants, functions))
                .collect();
            Ok(Term::App {
                function: fun_sym,
                args: translated?,
            })
        }
    }
}

fn build_constant_map(sig: &Signature) -> HashMap<String, FunctionSymbol> {
    sig.constants
        .iter()
        .map(|c| (c.name.clone(), c.clone()))
        .collect()
}

fn build_function_map(sig: &Signature) -> HashMap<String, FunctionSymbol> {
    sig.functions
        .iter()
        .map(|f| (f.name.clone(), f.clone()))
        .collect()
}

fn build_relation_map(sig: &Signature) -> HashMap<String, RelationSymbol> {
    sig.relations
        .iter()
        .map(|r| (r.name.clone(), r.clone()))
        .collect()
}

// ---------- Formula pretty-printing for error messages ----------

/// Best-effort surface rendering of a [`Formula`].  Used in error
/// messages — not meant to round-trip the FOL grammar exactly.
pub fn format_formula(f: &Formula) -> String {
    let mut out = String::new();
    render_formula(f, &mut out);
    out
}

fn render_formula(f: &Formula, out: &mut String) {
    match f {
        Formula::Top => out.push_str("true"),
        Formula::Bot => out.push_str("false"),
        Formula::Atom { relation, args } => {
            out.push_str(&relation.name);
            out.push('(');
            for (i, t) in args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                render_term(t, out);
            }
            out.push(')');
        }
        Formula::NegAtom { relation, args } => {
            out.push('~');
            out.push_str(&relation.name);
            out.push('(');
            for (i, t) in args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                render_term(t, out);
            }
            out.push(')');
        }
        Formula::Eq(a, b) => {
            render_term(a, out);
            out.push_str(" = ");
            render_term(b, out);
        }
        Formula::Neq(a, b) => {
            render_term(a, out);
            out.push_str(" != ");
            render_term(b, out);
        }
        Formula::And(l, r) => {
            out.push('(');
            render_formula(l, out);
            out.push_str(" /\\ ");
            render_formula(r, out);
            out.push(')');
        }
        Formula::Or(l, r) => {
            out.push('(');
            render_formula(l, out);
            out.push_str(" \\/ ");
            render_formula(r, out);
            out.push(')');
        }
        Formula::Forall { sort, body } => {
            out.push_str("forall : ");
            out.push_str(&sort.name);
            out.push_str(" . ");
            render_formula(body, out);
        }
        Formula::Exists { sort, body } => {
            out.push_str("exists : ");
            out.push_str(&sort.name);
            out.push_str(" . ");
            render_formula(body, out);
        }
        Formula::Not(inner) => {
            out.push('~');
            render_formula(inner, out);
        }
    }
}

fn render_term(t: &Term, out: &mut String) {
    match t {
        Term::Var(i) => {
            out.push('v');
            out.push_str(&i.to_string());
        }
        Term::App { function, args } => {
            out.push_str(&function.name);
            if !args.is_empty() {
                out.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    render_term(a, out);
                }
                out.push(')');
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(s: &str) -> Result<(Signature, Vec<Formula>), ParseError> {
        FolParser.parse(s)
    }

    #[test]
    fn test_parse_sort_decl() {
        let (sig, axioms) = parse("sort Elem.").expect("ok");
        assert_eq!(sig.sorts.len(), 1);
        assert!(axioms.is_empty());
    }

    #[test]
    fn test_parse_rel_decl() {
        let (sig, _) = parse("sort S. rel R : S, S.").expect("ok");
        assert_eq!(sig.relations.len(), 1);
        let r = sig.relations.iter().next().expect("one");
        assert_eq!(r.name, "R");
        assert_eq!(r.arity.len(), 2);
    }

    #[test]
    fn test_parse_func_decl() {
        let (sig, _) = parse("sort S. func f : S -> S.").expect("ok");
        assert_eq!(sig.functions.len(), 1);
        let f = sig.functions.iter().next().expect("one");
        assert_eq!(f.name, "f");
        assert_eq!(f.domain.len(), 1);
    }

    #[test]
    fn test_parse_const_decl() {
        let (sig, _) = parse("sort S. const c : S.").expect("ok");
        assert_eq!(sig.functions.len(), 1);
        assert_eq!(sig.constants.len(), 1);
    }

    #[test]
    fn test_parse_axiom_atom() {
        let (_, axioms) = parse("sort S. rel P : S. axiom forall x : S . P(x).").expect("ok");
        assert_eq!(axioms.len(), 1);
        match &axioms[0] {
            Formula::Forall { body, .. } => match body.as_ref() {
                Formula::Atom { args, .. } => {
                    assert_eq!(args.len(), 1);
                    assert_eq!(args[0], Term::Var(0));
                }
                other => panic!("expected Atom, got {other:?}"),
            },
            other => panic!("expected Forall, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_axiom_conjunction() {
        let src = "sort S. rel P : S. rel Q : S. \
                   axiom forall x : S . P(x) /\\ Q(x).";
        let (_, axioms) = parse(src).expect("ok");
        // After to_nnf: Forall { And(P(x), Q(x)) }.
        match &axioms[0] {
            Formula::Forall { body, .. } => match body.as_ref() {
                Formula::And(_, _) => {}
                other => panic!("expected And, got {other:?}"),
            },
            other => panic!("expected Forall, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_implication_desugar() {
        // A -> B desugars to (~A) \/ B, then to_nnf pushes ~ to atoms.
        let src = "sort S. rel P : S. rel Q : S. \
                   axiom forall x : S . P(x) -> Q(x).";
        let (_, axioms) = parse(src).expect("ok");
        match &axioms[0] {
            Formula::Forall { body, .. } => match body.as_ref() {
                Formula::Or(l, r) => match (l.as_ref(), r.as_ref()) {
                    (Formula::NegAtom { .. }, Formula::Atom { .. }) => {}
                    (a, b) => panic!("expected Or(NegAtom, Atom), got Or({a:?}, {b:?})"),
                },
                other => panic!("expected Or, got {other:?}"),
            },
            other => panic!("expected Forall, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_biconditional_desugar() {
        let src = "sort S. rel P : S. rel Q : S. \
                   axiom forall x : S . P(x) <-> Q(x).";
        let (_, axioms) = parse(src).expect("ok");
        // (A <-> B) = ((~A \/ B) /\ (~B \/ A)) which after NNF stays And of two Or.
        match &axioms[0] {
            Formula::Forall { body, .. } => match body.as_ref() {
                Formula::And(left, right) => match (left.as_ref(), right.as_ref()) {
                    (Formula::Or(_, _), Formula::Or(_, _)) => {}
                    (a, b) => panic!("expected And(Or, Or), got And({a:?}, {b:?})"),
                },
                other => panic!("expected And, got {other:?}"),
            },
            other => panic!("expected Forall, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_nested_quantifiers() {
        let src = "sort S. rel R : S, S. \
                   axiom forall x : S . exists y : S . R(x, y).";
        let (_, axioms) = parse(src).expect("ok");
        // Expected: Forall { Exists { Atom { R, [Var(1), Var(0)] } } }
        match &axioms[0] {
            Formula::Forall { body, .. } => match body.as_ref() {
                Formula::Exists { body, .. } => match body.as_ref() {
                    Formula::Atom { args, .. } => {
                        assert_eq!(args, &vec![Term::Var(1), Term::Var(0)]);
                    }
                    other => panic!("expected Atom, got {other:?}"),
                },
                other => panic!("expected Exists, got {other:?}"),
            },
            other => panic!("expected Forall, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_unicode() {
        let src_ascii =
            "sort S. rel P : S. axiom forall x : S . P(x).";
        let src_unicode = "sort S. rel P : S. axiom ∀ x : S . P(x).";
        let (_, a1) = parse(src_ascii).expect("ascii ok");
        let (_, a2) = parse(src_unicode).expect("unicode ok");
        assert_eq!(a1, a2);
    }

    #[test]
    fn test_parse_comments() {
        let line = "-- this is a comment\nsort S.";
        let block = "{- block\ncomment -} sort S.";
        let (sig_a, _) = parse(line).expect("ok line");
        let (sig_b, _) = parse(block).expect("ok block");
        assert_eq!(sig_a.sorts.len(), 1);
        assert_eq!(sig_b.sorts.len(), 1);
    }

    #[test]
    fn test_parse_free_variable_error() {
        let err = parse("sort S. rel P : S. axiom P(x).").expect_err("should fail");
        assert!(matches!(err, ParseError::FreeVariables { .. }));
    }

    #[test]
    fn test_parse_undefined_sort_error() {
        let err = parse("rel R : Foo.").expect_err("should fail");
        // The SignatureError → ParseError conversion routes this to
        // UndefinedSort.
        assert!(matches!(err, ParseError::UndefinedSort { .. }));
    }

    #[test]
    fn test_parse_sorting_spec() {
        let src = include_str!("../../../specs/sorting/sort.fol");
        let (sig, axioms) = parse(src).expect("sort.fol should parse");
        assert_eq!(sig.sorts.len(), 1);
        assert_eq!(sig.relations.len(), 3);
        assert_eq!(sig.functions.len(), 1);
        assert_eq!(axioms.len(), 2);
    }

    #[test]
    fn test_parse_stack_spec() {
        let src = include_str!("../../../specs/stack/stack.fol");
        let (sig, axioms) = parse(src).expect("stack.fol should parse");
        assert_eq!(sig.sorts.len(), 2);
        assert_eq!(sig.relations.len(), 1);
        assert_eq!(sig.functions.len(), 3);
        assert_eq!(axioms.len(), 3);
    }

    #[test]
    fn test_roundtrip_nnf() {
        let src = "sort S. rel P : S. rel Q : S. \
                   axiom forall x : S . ~(P(x) /\\ Q(x)).";
        let (_, axioms) = parse(src).expect("ok");
        // After NNF, ~(P /\ Q) becomes ~P \/ ~Q.  No raw Not wrapping
        // non-atomic subformulas.
        assert!(no_non_atomic_not(&axioms[0]));
    }

    fn no_non_atomic_not(f: &Formula) -> bool {
        match f {
            Formula::Not(_) => false,
            Formula::And(l, r) | Formula::Or(l, r) => {
                no_non_atomic_not(l) && no_non_atomic_not(r)
            }
            Formula::Forall { body, .. } | Formula::Exists { body, .. } => {
                no_non_atomic_not(body)
            }
            _ => true,
        }
    }

    #[test]
    fn test_roundtrip_sentences() {
        let src = include_str!("../../../specs/sorting/sort.fol");
        let (_, axioms) = parse(src).expect("ok");
        for ax in &axioms {
            assert!(ax.is_sentence(), "axiom not a sentence: {ax:?}");
        }
    }
}
