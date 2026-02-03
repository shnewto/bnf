#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct InputRangeOffset {
    pub start: usize,
    pub len: usize,
}

impl InputRangeOffset {
    pub const fn total_len(&self) -> usize {
        self.start + self.len
    }
}

/// A sliding window over the input strings being parsed.
#[derive(Clone, Copy)]
pub(crate) struct InputRange<'gram> {
    input: &'gram str,
    pub offset: InputRangeOffset,
}

impl<'gram> InputRange<'gram> {
    pub const fn new(input: &'gram str) -> Self {
        Self {
            input,
            offset: InputRangeOffset { start: 0, len: 0 },
        }
    }
    /// Remaining input from the current position (slice; does not allocate).
    #[inline(always)]
    pub fn next(&self) -> &'gram str {
        let next_idx = self.offset.start + self.offset.len;
        self.input.get(next_idx..).unwrap_or("")
    }
    pub const fn after(&self) -> Self {
        Self {
            input: self.input,
            offset: InputRangeOffset {
                start: self.offset.start + self.offset.len,
                len: 0,
            },
        }
    }
    #[mutants::skip]
    pub fn advance_by(&self, step: usize) -> Self {
        let InputRangeOffset { start, len } = self.offset;
        let max_len = self.input.len() - start;
        let len = std::cmp::min(len + step, max_len);
        Self {
            input: self.input,
            offset: InputRangeOffset { start, len },
        }
    }
    pub const fn is_complete(&self) -> bool {
        self.offset.start == 0 && self.offset.len == self.input.len()
    }
}

/// A clear view of [`InputRange`], in the format "InputRange(before | current | after)"
/// e.g., "[`InputRange`](["1", "+", "("] | ["2"] | ["*", "3", "-", "4", ")"])"
impl std::fmt::Debug for InputRange<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let InputRangeOffset { start, len, .. } = self.offset;
        let before = self.input.get(..start).unwrap_or("");
        let scanned = self
            .input
            .get(start..)
            .and_then(|s| s.get(..len))
            .unwrap_or("");
        let after = self.input.get(start + len..).unwrap_or("");
        write!(f, "InputRange(\"{before}|{scanned}|{after}\")",)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn advance_by_respects_input_bounds() {
        // Range at start=1, len=0 over "ab" (len 2). advance_by(2) must cap at 1 (only one byte left).
        let r = InputRange::new("ab").advance_by(1).after().advance_by(2);
        assert_eq!(r.offset.start, 1);
        assert_eq!(
            r.offset.len, 1,
            "advance_by must not exceed input.len() - start"
        );
    }

    #[test]
    fn debug_fmt() {
        let input = "GATTACA";
        let input_range = InputRange::new(input).advance_by(3).after().advance_by(2);

        let debug_format = format!("{input_range:?}");

        assert_eq!(debug_format, "InputRange(\"GAT|TA|CA\")");
    }
}
