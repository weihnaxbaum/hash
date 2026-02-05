use std::ops::{Index, IndexMut};

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

impl<K: Hash + Eq, V> IndexMut<K> for HashMap<K, V> {
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        match self.get_mut(key) {
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
        while offset != self.data.len()
            && let Some((k, v)) = &self.data[(hash + offset) % self.data.len()]
        {
            if key == *k {
                return Some(v);
            }
            offset += 1;
        }
        None
    }

    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        let hash = Self::usize_hash(&key);
        let data_len = self.data.len();
        for offset in 0..data_len {
            let i = (hash + offset) % data_len;
            match &self.data[i] {
                Some((k, _)) if key == *k => return Some(&mut self.data[i].as_mut().unwrap().1),
                None => return None,
                _ => {}
            }
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

pub struct HashSet<T: Hash + Eq>(HashMap<T, ()>);

// derive requires T to impl Default
impl<T: Hash + Eq> Default for HashSet<T> {
    fn default() -> Self {
        Self(HashMap::default())
    }
}

impl<T: Hash + Eq> HashSet<T> {
    pub fn with_capacity(n: usize) -> Self {
        Self(HashMap::with_capacity(n))
    }

    pub fn contains(&self, val: T) -> bool {
        self.0.contains(val)
    }

    pub fn insert(&mut self, val: T) -> bool {
        self.0.insert(val, ()).is_none()
    }

    pub fn insert_without_grow(&mut self, val: T) -> bool {
        self.0.insert_without_grow(val, ()).is_none()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(PartialEq, Eq)]
    struct SameHash(u32);

    impl Hash for SameHash {
        fn hash(&self) -> u64 {
            if self.0.is_multiple_of(2) { 0 } else { 123456 }
        }
    }

    #[test]
    fn basic_map() {
        let mut map = HashMap::default();
        assert!(map.is_empty());
        assert_eq!(map.insert(1, 1), None);
        assert_eq!(map.insert(1, 2), Some(1));
        assert_eq!(map.insert(2, 4), None);
        assert_eq!(map.len(), 2);
        assert!(!map.contains(0));
        assert_eq!(map[1], 2);
        assert_eq!(map[2], 4);
        map[2] += 1;
        assert_eq!(map[2], 5);
    }

    #[test]
    fn large_map() {
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

    #[test]
    fn same_hash_map() {
        const LEN: u32 = 100;
        let mut map = HashMap::default();
        for i in 0..LEN {
            map.insert(SameHash(i), i);
        }
        for i in 0..LEN {
            assert_eq!(map[SameHash(i)], i);
        }
    }

    #[test]
    fn rand_data() {
        let data = (0..1000).map(|mut x| {
            x ^= x << 13;
            x ^= x >> 17;
            (x << 5) % 100
        });
        let mut std_map = std::collections::HashMap::new();
        let mut map = HashMap::default();
        for n in data {
            match std_map.get_mut(&n) {
                Some(v) => *v += 1,
                None => {
                    std_map.insert(n, 1);
                }
            }
            match map.get_mut(n) {
                Some(v) => *v += 1,
                None => {
                    map.insert(n, 1);
                }
            };
        }
        for (k, v) in std_map {
            assert_eq!(v, map[k]);
        }
    }

    #[test]
    fn basic_set() {
        let mut set = HashSet::default();
        assert!(set.is_empty());
        assert!(set.insert(1));
        assert!(!set.insert(1));
        assert!(set.insert(2));
        assert_eq!(set.len(), 2);
        assert!(!set.contains(0));
        assert!(set.contains(1));
        assert!(set.contains(2));
    }

    #[test]
    fn large_set() {
        const LEN: u32 = 100_000;
        let mut set = HashSet::default();
        for i in 0..LEN {
            set.insert(i);
        }
        assert_eq!(set.len(), LEN as usize);
        for i in 0..LEN {
            assert!(set.contains(i));
        }
        assert!(!set.contains(LEN));
    }

    #[test]
    fn same_hash_set() {
        const LEN: u32 = 100;
        let mut set = HashSet::default();
        for i in 0..LEN {
            set.insert(SameHash(i));
        }
        for i in 0..LEN {
            assert!(set.contains(SameHash(i)));
        }
        assert!(!set.contains(SameHash(LEN)));
    }
}
