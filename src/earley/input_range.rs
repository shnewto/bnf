#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct InputRangeOffset {
    pub start: usize,
    pub len: usize,
}

impl InputRangeOffset {
    pub fn total_len(&self) -> usize {
        self.start + self.len
    }
}

/// A sliding window over the input strings being parsed.
#[derive(Clone)]
pub(crate) struct InputRange<'gram> {
    input: &'gram str,
    pub offset: InputRangeOffset,
}

impl<'gram> InputRange<'gram> {
    pub fn new(input: &'gram str) -> Self {
        Self {
            input,
            offset: InputRangeOffset { start: 0, len: 0 },
        }
    }
    pub fn next(&self) -> &'gram str {
        let next_idx = self.offset.start + self.offset.len;
        &self.input[next_idx..]
    }
    pub fn after(&self) -> Self {
        Self {
            input: self.input,
            offset: InputRangeOffset {
                start: self.offset.start + self.offset.len,
                len: 0,
            },
        }
    }
    pub fn advance_by(&self, step: usize) -> Self {
        let InputRangeOffset { start, len } = self.offset;
        let max_len = self.input.len() - start;
        let len = std::cmp::min(len + step, max_len);
        Self {
            input: self.input,
            offset: InputRangeOffset { start, len },
        }
    }
}

/// A clear view of [`InputRange`], in the format "InputRange(before | current | after)"
/// e.g., "InputRange(["1", "+", "("] | ["2"] | ["*", "3", "-", "4", ")"])"
impl<'gram> std::fmt::Debug for InputRange<'gram> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let InputRangeOffset { start, len, .. } = self.offset;
        let before = &self.input[..start];
        let scanned = &self.input[start..][..len];
        let after = &self.input[start..][len..];
        write!(f, "InputRange(\"{before}|{scanned}|{after}\")",)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn debug_fmt() {
        let input = "GATTACA";
        let input_range = InputRange::new(input).advance_by(3).after().advance_by(2);

        let debug_format = format!("{input_range:?}");

        assert_eq!(debug_format, "InputRange(\"GAT|TA|CA\")");
    }
}
