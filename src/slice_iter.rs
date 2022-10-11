/// Generic Iterator wrapper of slice
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SliceIter<'a, T> {
    pub(crate) slice: &'a [T],
}

impl<'a, T> Iterator for SliceIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.slice.split_first().map(|(first, rest)| {
            self.slice = rest;
            first
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.slice.len();
        (size, Some(size))
    }
}

/// Generic Iterator wrapper of mutable slice
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct SliceIterMut<'a, T> {
    pub(crate) slice: &'a mut [T],
}

impl<'a, T> Iterator for SliceIterMut<'a, T> {
    type Item = &'a mut T;
    fn next(&mut self) -> Option<Self::Item> {
        match std::mem::take(&mut self.slice) {
            [] => None,
            [first, rest @ ..] => {
                self.slice = rest;
                Some(first)
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.slice.len();
        (size, Some(size))
    }
}
