use core::fmt;

pub struct PadAdapter<'a, 'b> {
    f: &'a mut fmt::Formatter<'b>,
    on_newline: bool,
}

impl<'a, 'b> PadAdapter<'a, 'b> {
    pub fn new(f: &'a mut fmt::Formatter<'b>) -> Self {
        Self {
            f,
            on_newline: true,
        }
    }

    pub fn write_str(&mut self, s: &str) -> fmt::Result {
        fmt::Write::write_str(self, s)
    }

    pub fn write_fmt(&mut self, fmt: fmt::Arguments) -> fmt::Result {
        fmt::Write::write_fmt(self, fmt)
    }
}

impl fmt::Write for PadAdapter<'_, '_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for s in s.split_inclusive('\n') {
            if self.on_newline {
                self.f.write_str("    ")?;
            }

            self.on_newline = s.ends_with('\n');
            self.f.write_str(s)?;
        }

        Ok(())
    }

    fn write_char(&mut self, c: char) -> fmt::Result {
        if self.on_newline {
            self.f.write_str("    ")?;
        }
        self.on_newline = c == '\n';
        self.f.write_char(c)
    }
}
