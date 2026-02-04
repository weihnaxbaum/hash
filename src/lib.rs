use std::ops::Index;

pub trait Hash {
    fn hash(&self) -> u64;
}

impl Hash for u8 {
    fn hash(&self) -> u64 {
        *self as u64
    }
}

impl Hash for i8 {
    fn hash(&self) -> u64 {
        self.cast_unsigned().hash()
    }
}

impl Hash for u16 {
    fn hash(&self) -> u64 {
        *self as u64
    }
}

impl Hash for i16 {
    fn hash(&self) -> u64 {
        self.cast_unsigned().hash()
    }
}

impl Hash for u32 {
    fn hash(&self) -> u64 {
        *self as u64
    }
}

impl Hash for i32 {
    fn hash(&self) -> u64 {
        self.cast_unsigned().hash()
    }
}

impl Hash for u64 {
    fn hash(&self) -> u64 {
        *self
    }
}

impl Hash for i64 {
    fn hash(&self) -> u64 {
        self.cast_unsigned().hash()
    }
}

impl Hash for u128 {
    fn hash(&self) -> u64 {
        ((*self >> 64) as u64).wrapping_add(*self as u64)
    }
}

impl Hash for i128 {
    fn hash(&self) -> u64 {
        self.cast_unsigned().hash()
    }
}

pub struct HashMap<K: Hash + Eq, V> {
    data: Box<[Option<(K, V)>]>,
    len: usize,
}

// derive requires K and V to impl Default
impl<K: Hash + Eq, V> Default for HashMap<K, V> {
    fn default() -> Self {
        Self {
            data: Box::new([]),
            len: 0,
        }
    }
}

impl<K: Hash + Eq, V> Index<K> for HashMap<K, V> {
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        match self.get(key) {
            Some(v) => v,
            None => panic!("Invalid HashMap index"),
        }
    }
}

impl<K: Hash + Eq, V> HashMap<K, V> {
    pub fn with_capacity(n: usize) -> Self {
        Self::with_data_len(n * 2)
    }

    pub fn get(&self, key: K) -> Option<&V> {
        let hash = Self::usize_hash(&key);
        let mut offset = 0;
        while let Some((k, v)) = &self.data[(hash + offset) % self.data.len()] {
            if key == *k {
                return Some(v);
            }
            offset += 1;
        }
        None
    }

    pub fn contains(&self, key: K) -> bool {
        self.get(key).is_some()
    }

    pub fn insert(&mut self, key: K, val: V) -> Option<V> {
        if (self.len + 1) > self.capacity() {
            self.grow();
        }
        self.insert_without_grow(key, val)
    }

    pub fn insert_without_grow(&mut self, key: K, val: V) -> Option<V> {
        let hash = Self::usize_hash(&key);
        let mut offset = 0;
        let data_len = self.data.len();
        while let Some((k, _)) = &self.data[(hash + offset) % data_len] {
            if key == *k {
                let prev = self.data[(hash + offset) % data_len].take();
                self.data[(hash + offset) % data_len] = Some((key, val));
                return Some(prev.unwrap().1);
            }
            offset += 1;
        }
        self.len += 1;
        self.data[(hash + offset) % data_len] = Some((key, val));
        None
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn capacity(&self) -> usize {
        self.data.len() / 2
    }

    fn usize_hash(key: &K) -> usize {
        (key.hash() & usize::MAX as u64) as usize
    }

    fn grow(&mut self) {
        let mut other = Self::with_data_len((self.data.len() * 2).max(1));
        std::mem::swap(&mut other, self);
        for (k, v) in other.data.into_iter().flatten() {
            self.insert_without_grow(k, v);
        }
    }

    fn with_data_len(n: usize) -> Self {
        let mut data = Box::new_uninit_slice(n);
        for e in &mut data {
            e.write(None);
        }
        Self {
            data: unsafe { data.assume_init() },
            len: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let mut map = HashMap::default();
        assert!(map.is_empty());
        assert_eq!(map.insert(1, 1), None);
        assert_eq!(map.insert(1, 2), Some(1));
        assert_eq!(map.insert(2, 4), None);
        assert_eq!(map.len(), 2);
        assert!(!map.contains(0));
        assert_eq!(map[1], 2);
        assert_eq!(map[2], 4);
    }

    #[test]
    fn many() {
        const LEN: u32 = 100_000;
        let mut map = HashMap::default();
        for i in 0..LEN {
            map.insert(i, i * 2);
        }
        assert_eq!(map.len(), LEN as usize);
        for i in 0..LEN / 2 {
            assert_eq!(map[i], i * 2);
            assert_eq!(map[i * 2], i * 4);
        }
    }

    #[derive(PartialEq, Eq)]
    struct SameHash(u32);

    impl Hash for SameHash {
        fn hash(&self) -> u64 {
            if self.0.is_multiple_of(2) { 0 } else { 123456 }
        }
    }

    #[test]
    fn same_hash() {
        let mut map = HashMap::default();
        for i in 0..100 {
            map.insert(SameHash(i), i);
        }
        for i in 0..100 {
            assert_eq!(map[SameHash(i)], i);
        }
    }
}
