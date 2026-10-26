use logos::Logos;
use std::fmt;

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    Ident(String),
    PrefixOp(String),
    Infix(String),
    Infix0(String),
    Infix1(String),
    Infix2(String),
    Subtractive(String),
    Infix3(String),
    Infix4(String),

    Int(i64),
    Char(char),
    Float(f64),
    Str(String),

    Equal,
    EqualEqual,
    Sharp,
    Ampersand,
    Quote,
    LParen,
    RParen,
    Star,
    Comma,
    MinusGreater,
    Dot,
    DotDot,
    DotLParen,
    DotLBracket,
    Colon,
    ColonColon,
    ColonEqual,
    Semi,
    SemiSemi,
    LBracket,
    LBracketBar,
    LessMinus,
    RBracket,
    Underscore,
    UnderUnder,
    LBrace,
    Bar,
    BarRBracket,
    RBrace,
    AmperAmper,
    BarBar,

    And,
    As,
    Begin,
    Do,
    Done,
    Downto,
    Else,
    End,
    Exception,
    For,
    Fun,
    Function,
    If,
    In,
    Let,
    Match,
    Mutable,
    Not,
    Of,
    Or,
    Pref,
    Rec,
    Then,
    To,
    Try,
    Type,
    Value,
    When,
    While,
    With,
}

#[derive(Clone, Debug, PartialEq)]
pub enum LexicalError {
    UnterminatedComment { start: usize },
    UnterminatedString { start: usize },
    IllegalCharacter { at: usize, ch: char },
    BadEscape { at: usize },
    IntOverflow { at: usize },
    SyntaxError { at: usize, msg: &'static str },
}

impl fmt::Display for LexicalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LexicalError::UnterminatedComment { start } => {
                write!(f, "comment not terminated (opened at {start})")
            }
            LexicalError::UnterminatedString { start } => {
                write!(f, "string literal not terminated (opened at {start})")
            }
            LexicalError::IllegalCharacter { at, ch } => {
                write!(f, "illegal character {ch:?} at {at}")
            }
            LexicalError::BadEscape { at } => write!(f, "bad escape sequence at {at}"),
            LexicalError::IntOverflow { at } => write!(f, "integer literal out of range at {at}"),
            LexicalError::SyntaxError { at, msg } => write!(f, "{msg} (at {at})"),
        }
    }
}

#[derive(Logos, Debug, PartialEq)]
#[logos(skip r"[ \t\r\n]+")]
enum RawTok {
    #[regex(r"[A-Za-z_][A-Za-z0-9_']*", |lex| lex.slice().to_owned())]
    Ident(String),
    #[regex(r"[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?", parse_float)]
    Float(f64),
    #[regex(r"[0-9]+", parse_int)]
    Int(i64),
    #[regex(r#""([^"\\]|\\.)*""#,
        |lex| decode_string(lex.slice()))]
    String(String),
    #[regex(r#"'([^'\\]|\\.)'"#,
        |lex| decode_char(lex.slice()))]
    Char(char),
    #[token(".(")]
    DotLParen,
    #[token(".[")]
    DotLBracket,
    #[token("..")]
    DotDot,
    #[token("-.")]
    SubtractiveDot,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("::")]
    ColonColon,
    #[token(":=")]
    ColonEqual,
    #[token(":")]
    Colon,
    #[token("'")]
    Quote,
    #[token(";;")]
    SemiSemi,
    #[token(";")]
    Semi,
    #[token(",")]
    Comma,
    #[token("#")]
    Sharp,
    #[regex(r#"[!$%&*+\-/<=>?@\^|~]+|\[\||\|\]|\.\(|\.\[|->|&&|\|\||<-|=="#)]
    Operator,
    #[token(".")]
    Dot,
}

fn parse_int(lex: &mut logos::Lexer<'_, RawTok>) -> Result<i64, ()> {
    lex.slice().parse().map_err(|_| ())
}

fn parse_float(lex: &mut logos::Lexer<'_, RawTok>) -> Result<f64, ()> {
    lex.slice().parse().map_err(|_| ())
}

fn decode_string(raw: &str) -> Result<String, ()> {
    decode_escaped(&raw[1..raw.len() - 1]).map(|chars| chars.into_iter().collect())
}

fn decode_char(raw: &str) -> Result<char, ()> {
    let chars = decode_escaped(&raw[1..raw.len() - 1])?;
    let mut chars = chars.into_iter();
    let value = chars.next().ok_or(())?;
    if chars.next().is_some() {
        return Err(());
    }
    Ok(value)
}

fn decode_escaped(raw: &str) -> Result<Vec<char>, ()> {
    let mut chars = raw.chars();
    let mut result = Vec::new();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            result.push(ch);
            continue;
        }
        let escaped = chars.next().ok_or(())?;
        result.push(match escaped {
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            'b' => '\x08',
            'f' => '\x0c',
            '\\' => '\\',
            '"' => '"',
            '\'' => '\'',
            'x' => {
                let hi = chars.next().and_then(|c| c.to_digit(16)).ok_or(())?;
                let lo = chars.next().and_then(|c| c.to_digit(16)).ok_or(())?;
                char::from_u32(hi * 16 + lo).ok_or(())?
            }
            _ => return Err(()),
        });
    }
    Ok(result)
}

pub struct Lexer {
    inner: std::vec::IntoIter<Result<(usize, Tok, usize), LexicalError>>,
}

impl Lexer {
    pub fn new(input: &str) -> Result<Self, LexicalError> {
        let source = strip_comments(input)?;
        let mut raw = RawTok::lexer(&source).spanned();
        let mut tokens = Vec::new();
        while let Some(item) = raw.next() {
            let span = item.1;
            let result = match item.0 {
                Ok(raw) => raw_to_tok(raw, &source[span.clone()], span.start),
                Err(()) => Err(LexicalError::IllegalCharacter {
                    at: span.start,
                    ch: source[span.clone()].chars().next().unwrap_or('\0'),
                }),
            };
            tokens.push(result.map(|tok| (span.start, tok, span.end)));
        }
        Ok(Self {
            inner: tokens.into_iter(),
        })
    }
}

impl Iterator for Lexer {
    type Item = Result<(usize, Tok, usize), LexicalError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

fn strip_comments(input: &str) -> Result<String, LexicalError> {
    let bytes = input.as_bytes();
    let mut output = bytes.to_vec();
    let mut index = 0;
    let mut depth = 0;
    let mut comment_start = 0;
    let mut string = false;
    let mut string_start = 0;
    let mut escaped = false;

    while index < bytes.len() {
        let ch = bytes[index] as char;
        if string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                string = false;
            }
            index += 1;
            continue;
        }
        if depth == 0 && ch == '"' {
            string = true;
            string_start = index;
            index += 1;
            continue;
        }
        if index + 1 < bytes.len() && bytes[index..index + 2] == *b"(*" {
            if depth == 0 {
                comment_start = index;
            }
            depth += 1;
            output[index..index + 2].fill(b' ');
            index += 2;
            continue;
        }
        if depth > 0 && index + 1 < bytes.len() && bytes[index..index + 2] == *b"*)" {
            depth -= 1;
            output[index..index + 2].fill(b' ');
            index += 2;
            continue;
        }
        if depth > 0 && ch != '\n' && ch != '\r' {
            output[index] = b' ';
        }
        index += 1;
    }
    if depth != 0 {
        return Err(LexicalError::UnterminatedComment {
            start: comment_start,
        });
    }
    if string {
        return Err(LexicalError::UnterminatedString {
            start: string_start,
        });
    }
    Ok(String::from_utf8(output).expect("comment replacement preserves UTF-8"))
}

fn raw_to_tok(raw: RawTok, text: &str, at: usize) -> Result<Tok, LexicalError> {
    let tok = match raw {
        RawTok::Ident(value) => match value.as_str() {
            "_" => Tok::Underscore,
            "__" => Tok::UnderUnder,
            "and" => Tok::And,
            "as" => Tok::As,
            "begin" => Tok::Begin,
            "do" => Tok::Do,
            "done" => Tok::Done,
            "downto" => Tok::Downto,
            "else" => Tok::Else,
            "end" => Tok::End,
            "exception" => Tok::Exception,
            "for" => Tok::For,
            "fun" => Tok::Fun,
            "function" => Tok::Function,
            "if" => Tok::If,
            "in" => Tok::In,
            "let" => Tok::Let,
            "match" => Tok::Match,
            "mutable" => Tok::Mutable,
            "not" => Tok::Not,
            "of" => Tok::Of,
            "or" => Tok::Or,
            "prefix" => Tok::Pref,
            "rec" => Tok::Rec,
            "then" => Tok::Then,
            "to" => Tok::To,
            "try" => Tok::Try,
            "type" => Tok::Type,
            "value" => Tok::Value,
            "when" => Tok::When,
            "while" => Tok::While,
            "with" => Tok::With,
            _ => Tok::Ident(value),
        },
        RawTok::Float(value) => Tok::Float(value),
        RawTok::Int(value) => Tok::Int(value),
        RawTok::String(value) => Tok::Str(value),
        RawTok::Char(value) => Tok::Char(value),
        RawTok::DotLParen => Tok::DotLParen,
        RawTok::DotLBracket => Tok::DotLBracket,
        RawTok::DotDot => Tok::DotDot,
        RawTok::SubtractiveDot => Tok::Subtractive("-.".to_owned()),
        RawTok::LParen => Tok::LParen,
        RawTok::RParen => Tok::RParen,
        RawTok::LBracket => Tok::LBracket,
        RawTok::RBracket => Tok::RBracket,
        RawTok::LBrace => Tok::LBrace,
        RawTok::RBrace => Tok::RBrace,
        RawTok::ColonColon => Tok::ColonColon,
        RawTok::ColonEqual => Tok::ColonEqual,
        RawTok::Colon => Tok::Colon,
        RawTok::Quote => Tok::Quote,
        RawTok::Dot => Tok::Dot,
        RawTok::SemiSemi => Tok::SemiSemi,
        RawTok::Semi => Tok::Semi,
        RawTok::Comma => Tok::Comma,
        RawTok::Sharp => Tok::Sharp,
        RawTok::Operator => operator_to_tok(text, at)?,
    };
    Ok(tok)
}

fn operator_to_tok(text: &str, at: usize) -> Result<Tok, LexicalError> {
    let tok = match text {
        "=" => Tok::Equal,
        "==" => Tok::EqualEqual,
        "#" => Tok::Sharp,
        "&" => Tok::Ampersand,
        "'" => Tok::Quote,
        "(" => Tok::LParen,
        ")" => Tok::RParen,
        "*" => Tok::Star,
        "," => Tok::Comma,
        "->" => Tok::MinusGreater,
        ".." => Tok::DotDot,
        ".(" => Tok::DotLParen,
        ".[" => Tok::DotLBracket,
        ":" => Tok::Colon,
        "::" => Tok::ColonColon,
        ":=" => Tok::ColonEqual,
        ";" => Tok::Semi,
        ";;" => Tok::SemiSemi,
        "[" => Tok::LBracket,
        "[|" => Tok::LBracketBar,
        "<-" => Tok::LessMinus,
        "]" => Tok::RBracket,
        "_" => Tok::Underscore,
        "__" => Tok::UnderUnder,
        "{" => Tok::LBrace,
        "|" => Tok::Bar,
        "|]" => Tok::BarRBracket,
        "}" => Tok::RBrace,
        "&&" => Tok::AmperAmper,
        "||" => Tok::BarBar,
        value if value == "-." || value.starts_with('-') => Tok::Subtractive(value.to_owned()),
        value if value.starts_with('!') => Tok::PrefixOp(value.to_owned()),
        value if value.starts_with("**") => Tok::Infix4(value.to_owned()),
        value if value.starts_with('*') || value.starts_with('/') || value.starts_with('%') => {
            Tok::Infix3(value.to_owned())
        }
        value if value.starts_with('+') => Tok::Infix2(value.to_owned()),
        value if value.starts_with('@') || value.starts_with('^') => Tok::Infix1(value.to_owned()),
        value
            if value.starts_with('=')
                || value.starts_with('<')
                || value.starts_with('>')
                || value.starts_with('|')
                || value.starts_with('&')
                || value.starts_with('$') =>
        {
            Tok::Infix0(value.to_owned())
        }
        value => Tok::Infix(value.to_owned()),
    };
    if text.is_empty() {
        return Err(LexicalError::IllegalCharacter { at, ch: '\0' });
    }
    Ok(tok)
}

#[cfg(test)]
mod tests {
    use super::{Lexer, LexicalError, Tok};

    fn tokens(input: &str) -> Vec<Tok> {
        Lexer::new(input)
            .unwrap()
            .map(|item| item.unwrap().1)
            .collect()
    }

    #[test]
    fn lexes_keywords_literals_and_operators() {
        assert_eq!(
            tokens("let x = 12 + 1.5;;"),
            vec![
                Tok::Let,
                Tok::Ident("x".into()),
                Tok::Equal,
                Tok::Int(12),
                Tok::Infix2("+".into()),
                Tok::Float(1.5),
                Tok::SemiSemi,
            ]
        );
    }

    #[test]
    fn supports_nested_comments_and_preserves_strings() {
        assert_eq!(
            tokens("(* outer (* inner *) *) \"(* not a comment *)\""),
            vec![Tok::Str("(* not a comment *)".into())]
        );
    }

    #[test]
    fn tokenizes_list_brackets_separately() {
        assert_eq!(
            tokens("[] [| 1 |]"),
            vec![
                Tok::LBracket,
                Tok::RBracket,
                Tok::LBracketBar,
                Tok::Int(1),
                Tok::BarRBracket,
            ]
        );
    }

    #[test]
    fn keeps_type_annotation_punctuation_separate() {
        assert_eq!(
            tokens("data:'a"),
            vec![
                Tok::Ident("data".into()),
                Tok::Colon,
                Tok::Quote,
                Tok::Ident("a".into())
            ]
        );
    }

    #[test]
    fn reports_unterminated_comments() {
        assert!(matches!(
            Lexer::new("(* missing"),
            Err(LexicalError::UnterminatedComment { start: 0 })
        ));
    }
}
