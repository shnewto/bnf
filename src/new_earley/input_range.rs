/// A sliding window over the input strings being parsed.
#[derive(Debug, Clone)]
pub(crate) struct InputRange<'gram> {
    input: &'gram str,
    start: usize,
    len: usize,
}

impl<'gram> InputRange<'gram> {
    pub fn new(input: &'gram str) -> Self {
        Self {
            input,
            start: 0,
            len: 0,
        }
    }
    pub fn next(&self) -> Option<&str> {
        let next_idx = self.start + self.len;
        self.input.get(next_idx..)
    }
    pub fn after(&self) -> Self {
        Self {
            input: self.input,
            start: self.start + self.len,
            len: 0,
        }
    }
    pub fn advance_by(&self, step: usize) -> Self {
        let max_len = self.input.len() - self.start;
        Self {
            input: self.input,
            start: self.start,
            len: std::cmp::min(self.len + step, max_len),
        }
    }
    pub fn is_complete(&self) -> bool {
        self.start == 0 && self.len == self.input.len()
    }
}
