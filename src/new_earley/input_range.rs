#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
            input: self.next(),
            offset: InputRangeOffset {
                start: self.offset.start + self.offset.len,
                len: 0,
            },
        }
    }
    pub fn advance_by(&self, step: usize) -> Self {
        let max_len = self.input.len() - self.offset.start;
        let len = std::cmp::min(self.offset.len + step, max_len);
        Self {
            input: self.input,
            offset: InputRangeOffset {
                start: self.offset.start,
                len,
            },
        }
    }
    pub fn is_complete(&self) -> bool {
        self.offset.start == 0 && self.offset.len == self.input.len()
    }
}

/// A clear view of `InputRange`, in the format "InputRange(before | current | after)"
/// e.g., "`InputRange`(["1", "+", "("] | ["2"] | ["*", "3", "-", "4", ")"])"
impl<'gram> std::fmt::Debug for InputRange<'gram> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let InputRangeOffset { start, len } = self.offset;
        let before = &self.input[..start];
        let scanned = &self.input[start..][..len];
        let after = &self.input[start..][len..];
        write!(f, "InputRange({before:?} | {scanned:?} | {after:?})")
    }
}
