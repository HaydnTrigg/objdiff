//! Demangler for Borland C++Builder / Delphi symbol names.
//!
//! Names start with `@` and separate scopes with `@`: `@Unit@TClass@Method$qqri`. The part after
//! the `$` that starts the calling convention (`$qqr` register, `$qqs` stdcall, `$q` cdecl) lists
//! the argument types. Delphi's `dcc32 -J` leaves out the signature and often the unit
//! (`@TClass@Method`). Special names: `@TClass@` is the VMT, `@$xp$6TClass` the RTTI,
//! `$bctr` / `$bdtr` constructors and destructors, and `@@Name` a compiler helper (`System.@Name`).
//!
//! The output uses Delphi notation: `TClass.Method(Integer, var TPoint, const AnsiString)`.

use alloc::{
    format,
    string::{String, ToString},
    vec::Vec,
};

/// Whether `name` looks like a Borland mangled name that is safe to demangle without being told
/// the mangling scheme (other compilers also emit `@` names).
pub fn is_borland_name(name: &str) -> bool {
    name.starts_with('@')
        && (name.contains("$q") || name.contains("$xq") || name.starts_with("@$xp$"))
}

pub fn demangle(name: &str) -> Option<String> {
    let body = name.strip_prefix('@')?;
    if let Some(rest) = body.strip_prefix("$xp$") {
        let mut parser = Parser::new(rest);
        let ty = parser.named_type()?;
        return parser.at_end().then(|| format!("TypeInfo({ty})"));
    }
    let (qualified, signature) = match find_signature(body) {
        Some(i) => (&body[..i], Some(&body[i + 1..])),
        None => (body, None),
    };
    let (parts, is_vmt) = qualified_parts(qualified)?;
    let qualified = parts.join(".");
    if is_vmt {
        return signature.is_none().then(|| format!("{qualified} VMT"));
    }
    let Some(signature) = signature else {
        return Some(qualified);
    };
    match parse_signature(signature) {
        Some((args, convention)) => Some(format!("{qualified}({}){convention}", args.join(", "))),
        None => Some(qualified),
    }
}

/// Position of the `$` that starts the function signature.
fn find_signature(body: &str) -> Option<usize> {
    let bytes = body.as_bytes();
    (1..bytes.len()).find(|&i| {
        bytes[i] == b'$'
            && bytes[i - 1] != b'@'
            && matches!(&bytes[i + 1..], [b'q', ..] | [b'x' | b'w', b'q', ..])
    })
}

/// Scope components; `@@Name` keeps the `@` of compiler helpers. A trailing `@` marks a VMT.
fn qualified_parts(qualified: &str) -> Option<(Vec<String>, bool)> {
    let mut parts = Vec::new();
    let mut helper = false;
    let mut is_vmt = false;
    let pieces = qualified.split('@').collect::<Vec<_>>();
    for (i, piece) in pieces.iter().enumerate() {
        if piece.is_empty() {
            if i + 1 == pieces.len() {
                is_vmt = i > 0;
            } else {
                helper = true;
            }
            continue;
        }
        let mut part = String::new();
        if helper {
            part.push('@');
            helper = false;
        }
        part.push_str(&special_name(piece));
        parts.push(part);
    }
    (!parts.is_empty()).then_some((parts, is_vmt))
}

fn special_name(name: &str) -> String {
    let Some(op) = name.strip_prefix("$b") else {
        return name.to_string();
    };
    let op = match op {
        "ctr" => return "Create".to_string(),
        "dtr" => return "Destroy".to_string(),
        "add" => "+",
        "sub" => "-",
        "mul" => "*",
        "div" => "/",
        "mod" => "%",
        "asg" => "=",
        "eql" => "==",
        "neq" => "!=",
        "lss" => "<",
        "gtr" => ">",
        "leq" => "<=",
        "geq" => ">=",
        "subs" => "[]",
        "call" => "()",
        "inc" => "++",
        "dec" => "--",
        "not" => "!",
        "land" => "&&",
        "lor" => "||",
        "new" => " new",
        "dele" => " delete",
        _ => return name.to_string(),
    };
    format!("operator{op}")
}

/// Returns the argument list and the calling convention suffix.
fn parse_signature(signature: &str) -> Option<(Vec<String>, &'static str)> {
    let mut parser = Parser::new(signature);
    // Const / volatile member functions
    while matches!(parser.peek(), Some(b'x' | b'w')) {
        parser.pos += 1;
    }
    let convention = parser.convention()?;
    let args = parser.arguments(false)?;
    parser.at_end().then_some((args, convention))
}

struct Parser<'a> {
    s: &'a [u8],
    pos: usize,
    /// Arguments of the current list, for back references
    args: Vec<String>,
}

impl<'a> Parser<'a> {
    fn new(s: &'a str) -> Self { Self { s: s.as_bytes(), pos: 0, args: Vec::new() } }

    fn at_end(&self) -> bool { self.pos >= self.s.len() }

    fn peek(&self) -> Option<u8> { self.s.get(self.pos).copied() }

    fn next(&mut self) -> Option<u8> {
        let c = self.peek()?;
        self.pos += 1;
        Some(c)
    }

    /// After `q`: `qqr` register (Delphi's default, not shown), `qqs` stdcall, `qqm` MS fastcall,
    /// otherwise cdecl.
    fn convention(&mut self) -> Option<&'static str> {
        if self.next()? != b'q' {
            return None;
        }
        if self.peek() == Some(b'q') {
            self.pos += 1;
            return match self.next()? {
                b'r' => Some(""),
                b's' => Some("; stdcall"),
                b'm' => Some("; msfastcall"),
                _ => None,
            };
        }
        Some("; cdecl")
    }

    /// Argument types up to the end (or `$` for a nested function type). `v` alone is no arguments.
    fn arguments(&mut self, nested: bool) -> Option<Vec<String>> {
        let saved = core::mem::take(&mut self.args);
        let mut args = Vec::new();
        if self.peek() == Some(b'v') && matches!(self.s.get(self.pos + 1), None | Some(b'$')) {
            self.pos += 1;
        } else {
            while let Some(c) = self.peek() {
                if nested && c == b'$' {
                    break;
                }
                let arg = self.ty()?;
                self.args.push(arg.clone());
                args.push(arg);
            }
        }
        self.args = saved;
        Some(args)
    }

    fn number(&mut self) -> Option<usize> {
        let start = self.pos;
        while self.peek().is_some_and(|c| c.is_ascii_digit()) {
            self.pos += 1;
        }
        core::str::from_utf8(&self.s[start..self.pos]).ok()?.parse().ok()
    }

    /// Length-prefixed, `@`-qualified type name.
    fn named_type(&mut self) -> Option<String> {
        let len = self.number()?;
        let name = self.s.get(self.pos..self.pos + len)?;
        self.pos += len;
        Some(core::str::from_utf8(name).ok()?.replace('@', "."))
    }

    fn ty(&mut self) -> Option<String> {
        Some(match self.next()? {
            b'x' => {
                let inner = self.ty()?;
                // `const` parameters passed by reference are just `const`
                format!("const {}", inner.strip_prefix("var ").unwrap_or(&inner))
            }
            b'w' => format!("volatile {}", self.ty()?),
            b'r' | b'h' => {
                let inner = self.ty()?;
                if inner.starts_with("const ") { inner } else { format!("var {inner}") }
            }
            b'p' => {
                let named = self.peek().is_some_and(|c| c.is_ascii_digit());
                let inner = self.ty()?;
                match inner.as_str() {
                    "void" | "const void" => "Pointer".to_string(),
                    "Char" => "PChar".to_string(),
                    "WideChar" => "PWideChar".to_string(),
                    // Delphi classes are pointers in C++ terms
                    _ if named => inner,
                    _ => format!("^{inner}"),
                }
            }
            b'u' => match self.next()? {
                b'c' => "Byte",
                b's' => "Word",
                b'i' => "Cardinal",
                b'l' => "LongWord",
                b'j' => "UInt64",
                _ => return None,
            }
            .to_string(),
            b'z' => match self.next()? {
                b'c' => "ShortInt".to_string(),
                _ => return None,
            },
            b'v' => "void".to_string(),
            b'c' => "Char".to_string(),
            b's' => "SmallInt".to_string(),
            b'i' => "Integer".to_string(),
            b'l' => "LongInt".to_string(),
            b'j' => "Int64".to_string(),
            b'f' => "Single".to_string(),
            b'd' => "Double".to_string(),
            b'g' => "Extended".to_string(),
            b'o' => "Boolean".to_string(),
            b'b' => "WideChar".to_string(),
            b'e' => "...".to_string(),
            b'0'..=b'9' => {
                self.pos -= 1;
                self.named_type()?
            }
            b'a' => {
                let len = self.number()?;
                if self.next()? != b'$' {
                    return None;
                }
                format!("array[0..{}] of {}", len.checked_sub(1)?, self.ty()?)
            }
            b'q' => {
                self.pos -= 1;
                let convention = self.convention()?;
                let args = self.arguments(true)?;
                if self.next()? != b'$' {
                    return None;
                }
                let result = self.ty()?;
                let args =
                    if args.is_empty() { String::new() } else { format!("({})", args.join(", ")) };
                if result == "void" {
                    format!("procedure{args}{convention}")
                } else {
                    format!("function{args}: {result}{convention}")
                }
            }
            b'M' => {
                let _class = self.ty()?;
                format!("{} of object", self.ty()?)
            }
            b't' => {
                let c = self.next()?;
                let index = match c {
                    b'1'..=b'9' => (c - b'1') as usize,
                    b'a'..=b'z' => (c - b'a') as usize + 9,
                    _ => return None,
                };
                self.args.get(index)?.clone()
            }
            _ => return None,
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn d(name: &str) -> String { demangle(name).unwrap_or_else(|| panic!("{name}")) }

    #[test]
    fn delphi() {
        assert_eq!(d("@System@@LStrArrayClr$qqrpvi"), "System.@LStrArrayClr(Pointer, Integer)");
        assert_eq!(d("@@LStrArrayClr$qqrpvi"), "@LStrArrayClr(Pointer, Integer)");
        assert_eq!(d("@TProbe@$bctr$qqri"), "TProbe.Create(Integer)");
        assert_eq!(d("@TProbe@$bdtr$qqrv"), "TProbe.Destroy()");
        assert_eq!(d("@TProbe@SetName$qqrx10AnsiString"), "TProbe.SetName(const AnsiString)");
        assert_eq!(d("@Fill$qqrr7TPoint3xd"), "Fill(var TPoint3, const Double)");
        assert_eq!(d("@@ClassCreate$qqrp10TMetaClasso"), "@ClassCreate(TMetaClass, Boolean)");
        assert_eq!(
            d("@System@TObject@SafeCallException$qqrp14System@TObjectpv"),
            "System.TObject.SafeCallException(System.TObject, Pointer)"
        );
        assert_eq!(
            d("@System@@LStrFromArray$qqrr17System@AnsiStringpci"),
            "System.@LStrFromArray(var System.AnsiString, PChar, Integer)"
        );
        assert_eq!(
            d("@Windows@MessageBox$qqspcpcui"),
            "Windows.MessageBox(PChar, PChar, Cardinal); stdcall"
        );
        assert_eq!(d("@Foo$qqrit1"), "Foo(Integer, Integer)");
        assert_eq!(d("@TProbe@"), "TProbe VMT");
        assert_eq!(d("@Probe@TProbe@"), "Probe.TProbe VMT");
        assert_eq!(d("@$xp$6TProbe"), "TypeInfo(TProbe)");
        assert_eq!(d("@$xp$17System@AnsiString"), "TypeInfo(System.AnsiString)");
        assert_eq!(d("@AddOne"), "AddOne");
        assert_eq!(d("@TProbe@Twice"), "TProbe.Twice");
    }

    #[test]
    fn detection() {
        assert!(is_borland_name("@TProbe@Twice$qqri"));
        assert!(is_borland_name("@$xp$6TProbe"));
        assert!(!is_borland_name("@1234"));
        assert!(!is_borland_name("@LOCAL@func@var"));
    }
}
