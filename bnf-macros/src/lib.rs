//! Procedural macros for the bnf crate.
//!
//! Provides [`grammar!`] which expands to a const/static grammar (no allocation).

use proc_macro2::{Delimiter, Ident, Literal, Span, TokenStream, TokenTree};
use quote::quote;
use std::iter::Peekable;

/// AST: one production has a LHS (nonterminal name) and a list of alternatives;
/// each alternative is a list of terms (nonterminal name or terminal string).
struct Production {
    lhs: String,
    alternatives: Vec<Vec<Term>>,
}

enum Term {
    Nonterminal(String),
    Terminal(String),
}

fn parse_grammar(
    tokens: Peekable<impl Iterator<Item = TokenTree>>,
) -> Result<Vec<Production>, String> {
    let mut productions = Vec::new();
    let mut toks = tokens;

    while toks.peek().is_some() {
        productions.push(parse_production(&mut toks)?);
        if matches!(toks.peek(), Some(TokenTree::Punct(p)) if p.as_char() == ';') {
            let _ = toks.next();
        }
    }

    (!productions.is_empty())
        .then_some(productions)
        .ok_or_else(|| "grammar! requires at least one production".to_string())
}

fn parse_production(
    toks: &mut Peekable<impl Iterator<Item = TokenTree>>,
) -> Result<Production, String> {
    // < lhs >
    let lhs = parse_nonterminal(toks)?;
    // ::=
    expect_punct(toks, ':')?;
    expect_punct(toks, ':')?;
    expect_punct(toks, '=')?;
    // alt ( | alt )*
    let mut alternatives = Vec::new();
    loop {
        let terms = parse_alternative(toks)?;
        alternatives.push(terms);
        if let Some(TokenTree::Punct(p)) = toks.peek() {
            if p.as_char() == '|' {
                let _ = toks.next();
                continue;
            }
            if p.as_char() == ';' {
                break;
            }
        }
        if toks.peek().is_none() {
            break;
        }
    }
    Ok(Production { lhs, alternatives })
}

fn parse_nonterminal(
    toks: &mut Peekable<impl Iterator<Item = TokenTree>>,
) -> Result<String, String> {
    expect_punct(toks, '<')?;
    let name = expect_ident(toks)?;
    expect_punct(toks, '>')?;
    Ok(name)
}

fn parse_alternative(
    toks: &mut Peekable<impl Iterator<Item = TokenTree>>,
) -> Result<Vec<Term>, String> {
    let mut terms = Vec::new();
    loop {
        if toks.peek().is_none() {
            break;
        }
        if let Some(TokenTree::Punct(p)) = toks.peek() {
            if p.as_char() == '|' || p.as_char() == ';' {
                break;
            }
        }
        let term = parse_term(toks)?;
        terms.push(term);
    }
    Ok(terms)
}

fn parse_term(toks: &mut Peekable<impl Iterator<Item = TokenTree>>) -> Result<Term, String> {
    let next = toks.next().ok_or("expected term")?;
    match &next {
        TokenTree::Punct(p) if p.as_char() == '<' => {
            let name = expect_ident(toks)?;
            expect_punct(toks, '>')?;
            Ok(Term::Nonterminal(name))
        }
        TokenTree::Ident(i) => Ok(Term::Terminal(i.to_string())),
        TokenTree::Literal(lit) => {
            let s = lit.to_string();
            let terminal = if s.starts_with('"') {
                s.trim_matches('"').replace('\\', "")
            } else if s.starts_with('\'') && s.len() >= 2 {
                s.trim_matches('\'').to_string()
            } else {
                s
            };
            Ok(Term::Terminal(terminal))
        }
        _ => Err("expected <nonterminal>, ident, or literal".to_string()),
    }
}

fn expect_punct(
    toks: &mut Peekable<impl Iterator<Item = TokenTree>>,
    c: char,
) -> Result<(), String> {
    match toks.next() {
        Some(TokenTree::Punct(p)) if p.as_char() == c => Ok(()),
        _ => Err(format!("expected '{c}'")),
    }
}

fn expect_ident(toks: &mut Peekable<impl Iterator<Item = TokenTree>>) -> Result<String, String> {
    match toks.next() {
        Some(TokenTree::Ident(i)) => Ok(i.to_string()),
        _ => Err("expected identifier".to_string()),
    }
}

fn term_to_tokens(t: &Term) -> TokenStream {
    match t {
        Term::Nonterminal(name) => {
            let lit = Literal::string(name);
            quote! { ::bnf::Term::nonterminal_const(#lit) }
        }
        Term::Terminal(s) => {
            let lit = Literal::string(s);
            quote! { ::bnf::Term::terminal_const(#lit) }
        }
    }
}

#[proc_macro]
pub fn grammar(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let tokens: Vec<TokenTree> = input.into_iter().collect();
    let mut toks = tokens.into_iter().peekable();

    let productions = match toks.peek() {
        Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Brace => {
            parse_grammar(g.stream().into_iter().peekable())
        }
        _ => parse_grammar(toks),
    };

    let productions = match productions {
        Ok(p) => p,
        Err(e) => {
            return syn::Error::new(Span::call_site(), e)
                .to_compile_error()
                .into();
        }
    };

    let span = Span::call_site();
    let mut term_statics = Vec::new();
    let mut expr_statics = Vec::new();
    let mut prod_array_elems = Vec::new();
    let mut term_idx = 0u32;
    let mut expr_idx = 0u32;

    for prod in &productions {
        let lhs_lit = Literal::string(&prod.lhs);
        let lhs_term = quote! { ::bnf::Term::nonterminal_const(#lhs_lit) };

        let mut expr_refs = Vec::new();
        for alt in &prod.alternatives {
            let static_terms_name = Ident::new(&format!("__bnf_terms_{term_idx}"), span);
            term_idx += 1;
            let term_exprs: Vec<_> = alt.iter().map(term_to_tokens).collect();
            let len = term_exprs.len();
            term_statics.push(quote! {
                static #static_terms_name: [::bnf::Term<'static>; #len] = [
                    #(#term_exprs),*
                ];
            });
            expr_refs.push(quote! { ::bnf::Expression::from_borrowed(&#static_terms_name) });
        }

        let static_exprs_name = Ident::new(&format!("__bnf_exprs_{expr_idx}"), span);
        expr_idx += 1;
        let num_alt = prod.alternatives.len();
        expr_statics.push(quote! {
            static #static_exprs_name: [::bnf::Expression<'static>; #num_alt] = [
                #(#expr_refs),*
            ];
        });

        prod_array_elems.push(quote! {
            ::bnf::Production::from_borrowed_rhs(#lhs_term, &#static_exprs_name)
        });
    }

    let num_prods = productions.len();
    let output = quote! {{
        #(#term_statics)*
        #(#expr_statics)*
        static __bnf_prods: [::bnf::Production<'static>; #num_prods] = [
            #(#prod_array_elems),*
        ];
        ::bnf::Grammar::from_borrowed(&__bnf_prods)
    }};

    output.into()
}
