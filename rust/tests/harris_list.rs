//! Concurrent map based on Harris's lock-free linked list
//! (<https://www.cl.cam.ac.uk/research/srg/netos/papers/2001-caslists.pdf>).

use atomic_arc::{Arc, ArcCell, OptionalArcCell};
use core::cmp::Ordering::{Equal, Greater, Less};

struct Node<K, V> {
  next: OptionalArcCell<Self>,
  key: K,
  value: V,
}

struct ListMap<K, V> {
  head: ArcCell<Node<K, V>>,
}

impl<K, V> Drop for ListMap<K, V> {
  fn drop(&mut self) {
    // Manual drop procedure to prevent a stack overflow.
    let prev = self.head.load();
    while let Some(curr) = prev.next.load() {
      prev.next.store(curr.next.load().as_ref());
    }
  }
}

impl<K, V> Default for ListMap<K, V>
where
  K: Ord + Default,
  V: Default,
{
  fn default() -> Self {
    Self::new()
  }
}

impl<K, V> Node<K, V>
where
  K: Default,
  V: Default,
{
  /// Creates a new node.
  fn new(key: K, value: V) -> Self {
    Self {
      next: OptionalArcCell::null(),
      key,
      value,
    }
  }

  /// Creates a dummy head.
  /// We never deref key and value of this head node.
  fn head() -> Self {
    Self {
      next: OptionalArcCell::null(),
      key: K::default(),
      value: V::default(),
    }
  }
}

struct Cursor<K, V> {
  // The previous node of `curr`.
  prev: Arc<Node<K, V>>,
  // Tag of `curr` should always be zero so when `curr` is stored in a `prev`, we don't store a
  // tagged pointer and cause cleanup to fail.
  curr: Option<Arc<Node<K, V>>>,
}

impl<K, V> Cursor<K, V> {
  /// Creates a cursor.
  fn new(head: &ArcCell<Node<K, V>>) -> Self {
    let prev = head.load();
    let curr = prev.next.load();
    Self { prev, curr }
  }

  fn value(&self) -> Option<&V> {
    self.curr.as_ref().map(|node| &node.value)
  }
}

impl<K: Ord, V> Cursor<K, V> {
  /// Clean up a chain of logically removed nodes in each traversal.
  #[inline]
  fn find_harris(&mut self, key: &K) -> Option<bool> {
    // Finding phase
    // - cursor.curr: first untagged node w/ key >= search key (4)
    // - cursor.prev: the ref of .next in previous untagged node (1 -> 2)
    // 1 -> 2 -x-> 3 -x-> 4 -> 5 -> ∅  (search key: 4)
    let mut prev_next = self.curr.clone();
    let found = loop {
      let Some(curr_node) = self.curr.as_ref() else {
        break false;
      };
      let (next, next_tag) = curr_node.next.load_with_tag();

      if next_tag != 0 {
        // We do not store tag so that `self.curr`s tag is always 0.
        self.curr = next;
        continue;
      }

      match curr_node.key.cmp(key) {
        Less => {
          self.prev = self.curr.clone().unwrap();
          self.curr = next.clone();
          prev_next = next;
        }
        Equal => break true,
        Greater => break false,
      }
    };

    // If prev and curr WERE adjacent, no need to clean up
    if prev_next.as_ref().map(|p| p.as_arc_ptr()) == self.curr.as_ref().map(|p| p.as_arc_ptr()) {
      return Some(found);
    }

    // cleanup tagged nodes between anchor and curr
    if !self
      .prev
      .next
      .compare_and_set(prev_next.as_ref(), self.curr.as_ref())
    {
      return None;
    }

    Some(found)
  }

  /// Inserts a value.
  #[inline]
  pub fn insert(&self, node: &Arc<Node<K, V>>) -> bool {
    node.next.store(self.curr.as_ref());

    self
      .prev
      .next
      .compare_and_set(self.curr.as_ref(), Some(node))
  }

  /// Removes the current node.
  #[inline]
  pub fn remove(&self) -> bool {
    let curr_node = self.curr.as_ref().unwrap();

    let next = curr_node.next.load();
    if !curr_node
      .next
      .compare_and_set_with_tag(next.as_ref(), 0, next.as_ref(), 1)
    {
      return false;
    }

    let _ = self
      .prev
      .next
      .compare_and_set(self.curr.as_ref(), next.as_ref());

    true
  }
}

impl<K, V> ListMap<K, V>
where
  K: Ord + Default,
  V: Default,
{
  /// Creates a new list.
  pub fn new() -> Self {
    ListMap {
      head: ArcCell::new(Node::head()),
    }
  }

  #[inline]
  fn get<F>(&self, key: &K, find: F) -> (bool, Cursor<K, V>)
  where
    F: Fn(&mut Cursor<K, V>, &K) -> Option<bool>,
  {
    loop {
      let mut cursor = Cursor::new(&self.head);
      if let Some(r) = find(&mut cursor, key) {
        return (r, cursor);
      }
    }
  }

  #[inline]
  fn insert<F>(&self, key: K, value: V, find: F) -> Result<(), Cursor<K, V>>
  where
    F: Fn(&mut Cursor<K, V>, &K) -> Option<bool>,
  {
    let node = Arc::new(Node::new(key, value));
    loop {
      let (found, cursor) = self.get(&node.key, &find);
      if found {
        return Err(cursor);
      }

      if cursor.insert(&node) {
        return Ok(());
      }
    }
  }

  #[inline]
  fn remove<F>(&self, key: &K, find: F) -> Option<Cursor<K, V>>
  where
    F: Fn(&mut Cursor<K, V>, &K) -> Option<bool>,
  {
    loop {
      let (found, cursor) = self.get(key, &find);
      if !found {
        return None;
      }

      if cursor.remove() {
        return Some(cursor);
      }
    }
  }

  pub fn harris_get(&self, key: &K) -> Option<Cursor<K, V>> {
    let (found, cursor) = self.get(key, Cursor::find_harris);
    if found {
      Some(cursor)
    } else {
      None
    }
  }

  pub fn harris_insert(&self, key: K, value: V) -> Result<(), Cursor<K, V>> {
    self.insert(key, value, Cursor::find_harris)
  }

  pub fn harris_remove(&self, key: &K) -> Option<Cursor<K, V>> {
    self.remove(key, Cursor::find_harris)
  }
}

#[test]
fn smoke() {
  extern crate rand;
  use crossbeam_utils::thread;
  use rand::prelude::*;

  const THREADS: i32 = 30;
  const ELEMENTS_PER_THREADS: i32 = 1000;

  let map = &ListMap::new();

  thread::scope(|s| {
    for t in 0..THREADS {
      s.spawn(move |_| {
        let rng = &mut rand::thread_rng();
        let mut keys: Vec<i32> = (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
        keys.shuffle(rng);
        for i in keys {
          assert!(map.harris_insert(i, i.to_string()).is_ok());
        }
      });
    }
  })
  .unwrap();

  thread::scope(|s| {
    for t in 0..(THREADS / 2) {
      s.spawn(move |_| {
        let rng = &mut rand::thread_rng();
        let mut keys: Vec<i32> = (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
        keys.shuffle(rng);
        for i in keys {
          assert_eq!(
            i.to_string(),
            *map
              .harris_remove(&i)
              .as_ref()
              .and_then(|cursor| cursor.value())
              .unwrap()
          );
        }
      });
    }
  })
  .unwrap();

  thread::scope(|s| {
    for t in (THREADS / 2)..THREADS {
      s.spawn(move |_| {
        let rng = &mut rand::thread_rng();
        let mut keys: Vec<i32> = (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
        keys.shuffle(rng);
        for i in keys {
          assert_eq!(
            i.to_string(),
            *map
              .harris_get(&i)
              .as_ref()
              .and_then(|cursor| cursor.value())
              .unwrap()
          );
        }
      });
    }
  })
  .unwrap();
}
