use std::{fmt, mem, ops, path::PathBuf, str};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Pos {
    offset: u32,
}

impl fmt::Debug for Pos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Pos({})", self.offset)
    }
}

#[derive(Clone, Copy)]
pub struct Span {
    start: Pos,
    len: u32,
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let &Self {
            start: Pos { offset },
            len: _len,
        } = self;

        write!(f, "Span({:?})", offset..offset + _len)
    }
}

impl Span {
    #[must_use]
    pub fn start(&self) -> Pos {
        self.start
    }
    #[must_use]
    pub fn end(&self) -> Pos {
        Pos {
            offset: self.start.offset + self.len,
        }
    }
    #[must_use]
    pub fn display<'a>(&self, source: &'a Source) -> SpanDisplay<'a> {
        let (line, col) = self.start.line_col(source);
        SpanDisplay {
            source,
            span: *self,
            line,
            col,
        }
    }
}

#[must_use]
#[derive(Clone)]
pub struct SpanDisplay<'a> {
    source: &'a Source,
    span: Span,
    line: u32,
    col: u32,
}

impl fmt::Display for SpanDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

        let line_start = (self.span.start.offset + 1 - self.col) as usize;
        writeln!(
            f,
            "At {}:{}:{}",
            self.source.path.display(),
            self.line,
            self.col
        )?;
        let mut index = line_start;

        let end = self.span.end();
        for line in self.source.code[line_start..].split('\n') {
            f.write_str("> ")?;
            f.write_str(line.trim_ascii_end())?;
            f.write_char('\n')?;

            index += line.len() + 1;
            if end.offset() <= index {
                break;
            }
        }

        Ok(())
    }
}

pub trait Spanned {
    #[must_use]
    fn span(&self) -> Span;
}

impl Pos {
    fn advance_by_char(&mut self, ch: char) {
        self.offset += ch.len_utf8() as u32;
    }
    fn advance_by_str(&mut self, s: &str) {
        self.offset += s.len() as u32;
    }

    #[must_use]
    pub fn to_span(self) -> Span {
        self.to(self)
    }
    #[must_use]
    pub fn to(self, end: Self) -> Span {
        Span {
            start: self,
            len: end.offset - self.offset,
        }
    }
    #[must_use]
    pub fn up_to(self, code: &CodeIter) -> Span {
        Span {
            start: self,
            len: code.pos().offset - self.offset,
        }
    }
    #[must_use]
    pub fn offset(&self) -> usize {
        self.offset as _
    }

    #[must_use]
    pub fn line_col(&self, source: &Source) -> (u32, u32) {
        let code_before = &source.code[..self.offset()];
        let line_start = code_before.rfind('\n').map_or(0, |i| i + 1);

        let line = 1 + code_before[..line_start]
            .bytes()
            .map(|b| (b == b'\n') as u32)
            .sum::<u32>();
        let col = (self.offset() - line_start + 1) as _;
        (line, col)
    }

    #[must_use]
    pub fn show<'a>(&self, source: &'a Source) -> PosDisplay<'a> {
        let (line, col) = self.line_col(source);

        PosDisplay {
            source,
            pos: *self,
            line,
            col,
        }
    }
}

#[derive(Clone)]
pub struct PosDisplay<'a> {
    source: &'a Source,
    pos: Pos,
    line: u32,
    col: u32,
}

impl fmt::Display for PosDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

        let line_start = (self.pos.offset + 1 - self.col) as usize;
        write!(
            f,
            "At {}:{}:{}\n> ",
            self.source.path.display(),
            self.line,
            self.col
        )?;
        f.write_str(self.source.code[line_start..].lines().next().unwrap_or(""))?;
        f.write_char('\n')?;

        Ok(())
    }
}

#[derive(Debug)]
pub struct Source {
    pub path: PathBuf,
    pub name: String,
    pub code: String,
}

#[derive(Debug, Clone)]
pub struct CodeIter<'a> {
    _source: &'a Source,
    pos: Pos,
    chars: str::Chars<'a>,
    is_newline_whitespace: bool,
}

impl<'a> CodeIter<'a> {
    #[must_use]
    pub fn new(source: &'a Source) -> Self {
        // TODO: handle in `Source` constructor
        assert!(source.code.len() <= u32::MAX as usize);

        Self {
            _source: source,
            pos: Pos { offset: 0 },
            chars: source.code.chars(),
            is_newline_whitespace: false,
        }
    }
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.as_str().is_empty()
    }
    #[must_use]
    pub fn as_str_until(&self, pos: Pos) -> &'a str {
        &self.as_str()[..pos.offset.saturating_sub(self.pos.offset) as usize]
    }
    #[must_use]
    pub fn as_str(&self) -> &'a str {
        self.chars.as_str()
    }
    #[must_use]
    pub fn as_bytes(&self) -> &'a [u8] {
        self.as_str().as_bytes()
    }
    #[must_use]
    pub fn pos(&self) -> Pos {
        self.pos
    }
    pub fn next_char(&mut self) -> Option<char> {
        let ch = self.chars.next()?;
        self.pos.advance_by_char(ch);
        Some(ch)
    }
    pub fn take_char_if(&mut self, f: impl FnOnce(char) -> bool) -> Option<char> {
        f(self.peek()?).then(|| self.next_char().unwrap())
    }
    pub fn skipn_bytes(&mut self, mut n: usize) {
        let s = self.chars.as_str();
        n = n.min(s.len());
        self.pos.advance_by_str(&s[..n]);
        self.chars = s[n..].chars();
    }
    #[must_use]
    pub fn peek(&self) -> Option<char> {
        self.chars.clone().next()
    }
    #[must_use]
    fn peekn(&self, n: usize) -> Option<char> {
        self.chars.clone().nth(n)
    }
    #[must_use]
    pub fn peek1(&self) -> Option<char> {
        self.peekn(1)
    }
    #[must_use]
    pub fn peek2(&self) -> Option<char> {
        self.peekn(2)
    }

    pub fn with_newline_whitespace_in<T>(
        &mut self,
        is_newline_whitespace: bool,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let prev_value = mem::replace(&mut self.is_newline_whitespace, is_newline_whitespace);
        let result = f(self);
        self.is_newline_whitespace = prev_value;
        result
    }
    #[must_use]
    pub fn with_newline_whitespace(
        &mut self,
        is_newline_whitespace: bool,
    ) -> CodeIterWithNewlineWhitespace<'a, '_> {
        let prev_val = mem::replace(&mut self.is_newline_whitespace, is_newline_whitespace);
        self.is_newline_whitespace = is_newline_whitespace;
        CodeIterWithNewlineWhitespace {
            restore_is_newline_whitespace: prev_val,
            code: self,
        }
    }
    pub fn skip_whitespace(&mut self) {
        let mut chars = self.chars.clone();
        let mut comment = false;
        while let Some(ch) = chars.next() {
            if ch == '\r' || ch == '\n' {
                comment = false;
                if !self.is_newline_whitespace {
                    break;
                }
            } else if ch == '#' {
                comment = true;
            } else if !ch.is_ascii_whitespace() && !comment {
                break;
            }
            self.pos.advance_by_char(ch);
            self.chars = chars.clone();
        }
    }
    pub fn skip_whitespace_and_newlines(&mut self) {
        self.with_newline_whitespace_in(true, Self::skip_whitespace);
    }
}

#[derive(Debug)]
pub struct CodeIterWithNewlineWhitespace<'a, 'b> {
    restore_is_newline_whitespace: bool,
    code: &'b mut CodeIter<'a>,
}

impl<'a, 'b> CodeIterWithNewlineWhitespace<'a, 'b> {
    pub fn restore(self) -> &'b mut CodeIter<'a> {
        let prev_val = self.restore_is_newline_whitespace;
        let slf = mem::MaybeUninit::new(self);
        let code = unsafe { std::ptr::read(&raw const (*slf.as_ptr()).code) };
        code.is_newline_whitespace = prev_val;
        code
    }
}

impl<'a> ops::Deref for CodeIterWithNewlineWhitespace<'a, '_> {
    type Target = CodeIter<'a>;
    fn deref(&self) -> &CodeIter<'a> {
        self.code
    }
}
impl<'a> ops::DerefMut for CodeIterWithNewlineWhitespace<'a, '_> {
    fn deref_mut(&mut self) -> &mut CodeIter<'a> {
        self.code
    }
}

impl Drop for CodeIterWithNewlineWhitespace<'_, '_> {
    fn drop(&mut self) {
        self.code.is_newline_whitespace = self.restore_is_newline_whitespace;
    }
}
