use atomic_arc::*;
use std::mem::MaybeUninit;

pub struct Queue<T> {
  head: ArcCell<Node<T>>,
  tail: ArcCell<Node<T>>,
}
struct Node<T> {
  value: MaybeUninit<T>,
  next: OptionalArcCell<Node<T>>,
}

impl<T> Queue<T> {
  pub fn new() -> Queue<T> {
    let node = Arc::new(Node {
      value: MaybeUninit::<T>::uninit(),
      next: OptionalArcCell::null(),
    });
    Queue {
      head: node.as_atomic(),
      tail: node.into_atomic(),
    }
  }

  pub fn enqueue(&self, value: T) {
    let node = Arc::new(Node {
      value: MaybeUninit::new(value),
      next: OptionalArcCell::null(),
    });
    // Keep trying until Enqueue is done
    loop {
      let tail = self.tail.load();
      let next = tail.next.load();
      // Are tail and next consistent?
      if tail.as_arc_ptr() == self.tail.peek() {
        match next {
          // Was tail pointing to the last node?
          None => {
            // Try to link node at the end of the linked list
            if tail.next.compare_and_set(None, Some(&node)) {
              // Enqueue is done.
              // Try to swing Tail to the inserted node
              self.tail.compare_and_set(&tail, &node);
              // Exit loop
              break;
            }
          }
          // Tail was not pointing to the last node
          Some(next_ptr) => {
            // Try to swing Tail to the next node
            self.tail.compare_and_set(&tail, &next_ptr);
          }
        }
      }
    }
  }

  pub fn dequeue(&self) -> Option<T> {
    loop {
      let head = self.head.load();
      let tail = self.tail.load();
      let next = head.next.load();
      if head.as_arc_ptr() == self.head.peek() {
        if head.as_arc_ptr() == tail.as_arc_ptr() {
          match next {
            None => return None,
            Some(n) => {
              self.tail.compare_and_set(&tail, &n);
            }
          }
        } else {
          match next {
            None => panic!("Corrupted queue"),
            Some(n) => {
              if self.head.compare_and_set(&head, &n) {
                return Some(unsafe { n.value.assume_init_read() });
              }
            }
          }
        }
      }
    }
  }
}

impl<T> Drop for Queue<T> {
  fn drop(&mut self) {
    while self.dequeue().is_some() {}
  }
}

#[cfg(test)]
mod test {
  use super::Queue;
  use atomic_arc::*;
  use core::sync::atomic::{AtomicU64, Ordering};

  static LATEST_DROP: AtomicU64 = AtomicU64::new(0);

  #[derive(Debug)]
  struct LogDrop {
    value: u64,
  }

  impl Drop for LogDrop {
    fn drop(&mut self) {
      LATEST_DROP.store(self.value, Ordering::SeqCst);
    }
  }

  #[test]
  fn litmus() {
    {
      let a = OptionalArcCell::new(LogDrop { value: 2903 });
      let b = Arc::new(LogDrop { value: 12345678 });

      let mut count = 0;
      for i in 0..(1 << 19) + (1 << 18) {
        drop(a.load());
        if (i & 0xFFFF) == 0 {
          assert_eq!(i, 65536 * count);
          count += 1;
        }
      }

      assert!(!a.compare_and_set(Some(&b), Some(&Arc::new(LogDrop { value: 20000 }))));
      assert_drop(20000);
      a.store(Some(&Arc::new(LogDrop { value: 20001 })));
      assert_drop(2903);
      a.store_consume(Some(Arc::new(LogDrop { value: 20002 })));
      assert_drop(20001);
      drop(a);
      assert_drop(20002);

      let queue = Queue::<LogDrop>::new();
      assert!(queue.dequeue().is_none());
      queue.enqueue(LogDrop { value: 10001 });
      queue.enqueue(LogDrop { value: 10002 });
      queue.enqueue(LogDrop { value: 10003 });
      queue.enqueue(LogDrop { value: 10004 });
      assert_eq!(queue.dequeue().map(|l| l.value), Some(10001));
      assert_drop(10001);
      assert_eq!(queue.dequeue().map(|l| l.value), Some(10002));
      assert_drop(10002);
      assert_eq!(queue.dequeue().map(|l| l.value), Some(10003));
      assert_drop(10003);

      drop(queue);
      assert_drop(10004);
    }
    assert_drop(12345678);
  }

  fn assert_drop(value: u64) {
    assert_eq!(LATEST_DROP.load(Ordering::SeqCst), value);
  }
}
