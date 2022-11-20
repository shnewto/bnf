#[derive(Debug, Clone)]
pub(crate) struct AppendOnlyVec<T, I> {
    vec: Vec<T>,
    id_type: std::marker::PhantomData<I>,
}

impl<T, I> AppendOnlyVec<T, I>
where
    I: From<usize> + Into<usize>,
{
    pub fn new() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        self.vec.len()
    }
    fn next_id(&self) -> I {
        I::from(self.len())
    }
    pub fn push(&mut self, item: T) -> I {
        let id = self.next_id();
        self.vec.push(item);
        id
    }
    pub fn push_with_id<F>(&mut self, build: F) -> &T
    where
        F: Fn(I) -> T,
    {
        let id = self.next_id();
        let item = build(id);
        let id = self.push(item);
        self.get(id).expect("failed to get appended item")
    }
    pub fn get(&self, id: I) -> Option<&T> {
        self.vec.get::<usize>(id.into())
    }
    pub fn get_mut(&mut self, id: I) -> Option<&mut T> {
        self.vec.get_mut::<usize>(id.into())
    }
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.vec.iter()
    }
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.vec.iter_mut()
    }
}

impl<T, K> Default for AppendOnlyVec<T, K> {
    fn default() -> Self {
        Self::from(vec![])
    }
}

impl<T, K> From<Vec<T>> for AppendOnlyVec<T, K> {
    fn from(vec: Vec<T>) -> Self {
        Self {
            vec,
            id_type: std::marker::PhantomData,
        }
    }
}

impl<T, K> IntoIterator for AppendOnlyVec<T, K> {
    type Item = <Vec<T> as IntoIterator>::Item;
    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.vec.into_iter()
    }
}

impl<'a, T, K> IntoIterator for &'a AppendOnlyVec<T, K> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.vec.iter()
    }
}

impl<'a, T, K> IntoIterator for &'a mut AppendOnlyVec<T, K> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.vec.iter_mut()
    }
}
