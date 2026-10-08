use miette::SourceSpan;
use std::ops::Range;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub const fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    pub fn to(self, other: Span) -> Self {
        Self::new(self.start, other.end)
    }

    pub fn range(self) -> Range<usize> {
        self.start as usize..self.end as usize
    }
}

impl From<Range<usize>> for Span {
    fn from(range: Range<usize>) -> Self {
        Self::new(range.start as u32, range.end as u32)
    }
}

impl From<Span> for SourceSpan {
    fn from(span: Span) -> Self {
        span.range().into()
    }
}
