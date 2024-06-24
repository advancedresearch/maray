//! Tokens for decoration.
//!
//! This design allows decorating expressions
//! in a flexible way that controls the text display.

use crate::Expr;
use serde::{Serialize, Deserialize};

/// Used to decorate expressions with extra information.
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Token {
    /// An expression.
    TokenExpr(Expr),
    /// `(`.
    StartParens,
    /// `)`.
    EndParens,
    /// `[`.
    StartSquareBracket,
    /// `]`.
    EndSquareBracket,
    /// `{`.
    StartCurlyBracket,
    /// `}`.
    EndCurlyBracket,
    /// `,`.
    Comma,
    /// ` `.
    Space,
    /// `\n`.
    NewLine,
    /// Tabs.
    Tabs,
    /// Tabs minus one level.
    TabsPrev,
}

impl Token {
    /// Returns if the token is a start bracket.
    pub fn is_start_bracket(&self) -> bool {
        use Token::*;

        match self {
            StartParens | StartSquareBracket | StartCurlyBracket => true,
            _ => false,
        }
    }
}

impl From<Expr> for Token {
    fn from(val: Expr) -> Token {Token::TokenExpr(val)}
}
