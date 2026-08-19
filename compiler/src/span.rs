//! Byte-offset spans and line/column mapping.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Span { start, end }
    }
    pub fn join(self, other: Span) -> Span {
        Span::new(self.start.min(other.start), self.end.max(other.end))
    }
}

/// Precomputed line-start table for a source file.
pub struct LineMap {
    line_starts: Vec<usize>,
}

impl LineMap {
    pub fn new(source: &str) -> Self {
        let mut line_starts = vec![0];
        for (i, b) in source.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i + 1);
            }
        }
        LineMap { line_starts }
    }

    /// 1-based (line, column) for a byte offset.
    pub fn line_col(&self, offset: usize) -> (usize, usize) {
        let line = self
            .line_starts
            .partition_point(|&s| s <= offset)
            .saturating_sub(1);
        (line + 1, offset - self.line_starts[line] + 1)
    }

    /// Byte range of a 1-based line, excluding the newline.
    pub fn line_span(&self, line: usize, source: &str) -> Span {
        let start = self.line_starts[line - 1];
        let end = self
            .line_starts
            .get(line)
            .map(|&s| s.saturating_sub(1))
            .unwrap_or(source.len());
        Span::new(start, end)
    }

    pub fn num_lines(&self) -> usize {
        self.line_starts.len()
    }
}
