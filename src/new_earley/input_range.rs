#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct InputRangeOffset {
    start: usize,
    len: usize,
}

/// A sliding window over the input strings being parsed.
#[derive(Debug, Clone)]
pub(crate) struct InputRange<'gram> {
    input: &'gram str,
    pub(crate) offset: InputRangeOffset,
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
