#[derive(Debug, Clone)]
pub(crate) struct AppendOnlyVec<T, K> {
    vec: Vec<T>,
    key_type: std::marker::PhantomData<K>,
}

impl<T, K> AppendOnlyVec<T, K>
where
    K: From<usize>,
    K: Into<usize>,
{
    pub fn new() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        self.vec.len()
    }
    fn next_key(&self) -> K {
        K::from(self.len())
    }
    pub fn push(&mut self, item: T) -> K {
        let key = self.next_key();
        self.vec.push(item);
        key
    }
    pub fn push_with_key<F>(&mut self, build: F) -> &T
    where
        F: Fn(K) -> T,
    {
        let key = self.next_key();
        let item = build(key);
        let key = self.push(item);
        self.get(key).expect("failed to get appended item")
    }
    pub fn get(&self, key: K) -> Option<&T> {
        self.vec.get::<usize>(key.into())
    }
    pub fn get_mut(&mut self, key: K) -> Option<&mut T> {
        self.vec.get_mut::<usize>(key.into())
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
            key_type: std::marker::PhantomData,
        }
    }
}
