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
