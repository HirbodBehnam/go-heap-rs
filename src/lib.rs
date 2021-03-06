//! # Go Heap in Rust
//!
//! `go_heap_rs` implements the Go's [heap](https://golang.org/pkg/container/heap/) interface in Rust
//! The heap it self is backed by another collection which it must implement the `Heap` trait for it
//!
//! # Advantages
//! * More control over swap method
//! * Added `fix` and `remove` methods
//! * Full access to underlying data
//!
//! # Disadvantages
//! * Must be backed by a collection like Vector
//! * Not really easy to work with
//! * Lack of some methods like `from`

use std::marker::PhantomData;

/// All types which you want to create heap from them must implement this trait
///
/// # Example of Min Heap
/// ```
/// use go_heap_rs::Heap;
/// struct MinHeap(Vec<i32>);
/// impl Heap<i32> for MinHeap {
///     fn len(&self) -> usize {
///         self.0.len()
///     }
///
///     fn less(&self, i: usize, j: usize) -> bool {
///         self.0[i] < self.0[j]
///     }
///
///     fn swap(&mut self, i: usize, j: usize) {
///         self.0.swap(i, j);
///     }
///
///     fn push(&mut self, x: i32) {
///         self.0.push(x);
///     }
///
///     fn pop(&mut self) -> i32 {
///         self.0.pop().expect("pop on an empty vec!")
///     }
///
///     fn peak(&self) -> Option<&i32> {
///         self.0.get(0)
///     }
/// }
/// ```
pub trait Heap<T> {
    /// length must return the length of the heap
    fn len(&self) -> usize;
    /// Compares two elements of the heap at i and j index
    /// It is guaranteed that the i and j are always valid
    fn less(&self, i: usize, j: usize) -> bool;
    /// This function must swap the i and j element in the heap array
    /// It is guaranteed that the i and j are always valid
    fn swap(&mut self, i: usize, j: usize);
    /// push is just like push in vector. It should add x to the last of array
    fn push(&mut self, x: T);
    /// This method should remove the last element of array and return it
    /// This function is guaranteed to be called when at least one element in available
    fn pop(&mut self) -> T;
    /// This method must return first element in your collection
    fn peak(&self) -> Option<&T>;
}

/// A heap structure which holds a type which derives from Heap
pub struct HeapType<T, E> where T: Heap<E> {
    pub data: T,
    #[doc(hidden)]
    phantom: PhantomData<E>,
}

impl<T: Heap<E>, E> HeapType<T, E> {
    /// Initialized a new heap from a Heap type
    ///
    /// # Arguments
    ///
    /// * `init`: The Heap type to be initialized
    ///
    /// returns: HeapType<T, E> which is your heap data structure
    ///
    /// # Examples
    ///
    /// ```
    /// use go_heap_rs::{HeapType, MinHeap};
    ///
    /// let my_vec = MinHeap(vec![4, 3, 2, 1]); // see min heap implementation in Heap trait
    /// let mut heap = HeapType::new(my_vec);
    /// assert_eq!(heap.peak(), Some(&1));
    /// ```
    pub fn new(init: T) -> HeapType<T, E> where T: Heap<E> {
        let mut data = HeapType {
            data: init,
            phantom: PhantomData,
        };
        // Init
        let n = data.data.len();
        if n != 0 {
            for i in (0..=n / 2 - 1).rev() {
                data.down(i, n);
            }
        }
        data
    }

    /// Pushes an element into heap
    ///
    /// # Arguments
    ///
    /// * `x`: The element to push it into heap
    pub fn push(&mut self, x: E) {
        self.data.push(x);
        self.up(self.data.len() - 1);
    }

    /// Removes the greatest item from the binary heap and returns it, or None if it is empty.
    ///
    /// returns E: The first element in list
    pub fn pop(&mut self) -> Option<E> {
        if self.data.len() == 0 { // empty heap
            return None;
        }
        let n = self.data.len() - 1;
        self.data.swap(0, n);
        self.down(0, n);
        Some(self.data.pop())
    }

    /// Removes an element from heap by it's index in it's underlying container
    ///
    /// # Arguments
    ///
    /// * `i`: The index to remove
    ///
    /// returns E: The element which as been removed
    ///
    /// # Panics
    /// This method might panic (based on implementation of `swap`) if `i` is bigger than `len()`
    ///
    /// # Examples
    ///
    /// ```
    /// use go_heap_rs::{HeapType, MinHeap};
    ///
    /// let my_vec = MinHeap(vec![1, 4, 3]);
    /// let mut heap = HeapType::new(my_vec); // [1, 4, 3]
    /// assert_eq!(heap.remove(1), 4);
    /// assert_eq!(heap.pop(), Some(1));
    /// assert_eq!(heap.pop(), Some(3));
    /// assert_eq!(heap.pop(), None);
    /// ```
    pub fn remove(&mut self, i: usize) -> E {
        let n = self.data.len() - 1;
        if n != i {
            self.data.swap(i, n);
            if !self.down(i, n) {
                self.up(i);
            }
        }
        self.data.pop()
    }


    /// Fix re-establishes the heap ordering after the element at index i has changed its value.
    /// Changing the value of the element at index i and then calling Fix is equivalent to,
    /// but less expensive than, calling Remove(h, i) followed by a Push of the new value.
    ///
    /// # Arguments
    ///
    /// * `i`: The index to fix
    ///
    /// # Examples
    ///
    /// ```
    /// use go_heap_rs::{HeapType, MinHeap};
    ///
    /// let my_vec = MinHeap(vec![10, 4, 3]);
    /// let mut heap = HeapType::new(my_vec); // [3, 4, 10]
    /// heap.data.0[1] = 0;
    /// heap.fix(0);
    /// assert_eq!(heap.pop(), Some(0));
    /// assert_eq!(heap.pop(), Some(3));
    /// assert_eq!(heap.pop(), Some(10));
    /// assert_eq!(heap.pop(), None);
    /// ```
    pub fn fix(&mut self, i: usize) {
        if !self.down(i, self.data.len()) {
            self.up(i);
        }
    }

    /// peak will return the top of heap if available
    pub fn peak(&self) -> Option<&E> {
        self.data.peak()
    }

    /// len will simply call `self.data.len()`
    pub fn len(&self) -> usize {
        self.data.len()
    }

    fn up(&mut self, mut j: usize) {
        loop {
            let i = (((j as isize) - 1) / 2) as usize; // parent
            if i == j || !self.data.less(j, i) {
                break;
            }
            self.data.swap(i, j);
            j = i
        }
    }

    fn down(&mut self, i0: usize, n: usize) -> bool {
        let mut i = i0;
        loop {
            let j1: isize = (2 * i + 1) as isize;
            if j1 >= n as isize || j1 < 0 { // j1 < 0 after int overflow
                break;
            }
            let mut j = j1 as usize; // left child
            let j2 = j1 as usize + 1;
            if j2 < n && self.data.less(j2, j1 as usize) {
                j = j2 // = 2*i + 2  // right child
            }
            if !self.data.less(j, i) {
                break;
            }
            self.data.swap(i, j);
            i = j
        }
        return i > i0;
    }
}

/// A very simple min heap implementation
pub struct MinHeap<T: Ord>(pub Vec<T>);

impl<T: Ord> Heap<T> for MinHeap<T> {
    fn len(&self) -> usize {
        self.0.len()
    }

    fn less(&self, i: usize, j: usize) -> bool {
        self.0[i] < self.0[j]
    }

    fn swap(&mut self, i: usize, j: usize) {
        self.0.swap(i, j);
    }

    fn push(&mut self, x: T) {
        self.0.push(x);
    }

    fn pop(&mut self) -> T {
        self.0.pop().expect("pop on an empty vec!")
    }

    fn peak(&self) -> Option<&T> {
        self.0.get(0)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Heap, HeapType, MinHeap};
    use std::collections::HashSet;
    use rand::{thread_rng, Rng};

    #[test]
    fn simple_vec() {
        // Create a vector
        let my_vec = MinHeap(vec![2, 4, 3, 1]);
        let mut heap = HeapType::new(my_vec);
        // Change it a bit
        assert_eq!(heap.peak().unwrap(), &1);
        assert_eq!(heap.pop().unwrap(), 1);
        heap.push(-1);
        assert_eq!(heap.pop().unwrap(), -1);
        assert_eq!(heap.pop().unwrap(), 2);
        assert_eq!(heap.pop().unwrap(), 3);
        assert_eq!(heap.pop().unwrap(), 4);
        assert_eq!(heap.data.len(), 0);
    }

    #[test]
    fn simple_remove() {
        let my_vec = MinHeap(vec![1, 4, 3]);
        let mut heap = HeapType::new(my_vec); // [1, 4, 3]
        assert_eq!(heap.remove(1), 4);
        assert_eq!(heap.pop(), Some(1));
        assert_eq!(heap.pop(), Some(3));
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn simple_fix() {
        let my_vec = MinHeap(vec![10, 4, 3]);
        let mut heap = HeapType::new(my_vec); // [3, 4, 10]
        heap.data.0[1] = 0;
        heap.fix(0);
        assert_eq!(heap.pop(), Some(0));
        assert_eq!(heap.pop(), Some(3));
        assert_eq!(heap.pop(), Some(10));
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn empty_test() {
        let mut heap = HeapType::new(MinHeap(vec![]));
        heap.push(2);
        heap.push(1);
        assert_eq!(heap.pop(), Some(1));
        assert_eq!(heap.pop(), Some(2));
        assert_eq!(heap.pop(), None);
    }

    //noinspection DuplicatedCode
    fn verify(h: &MinHeap<i32>, i: usize) {
        let n = h.len();
        let j1 = 2 * i + 1;
        let j2 = 2 * i + 2;
        if j1 < n {
            assert!(!h.less(j1, i), "heap invariant invalidated [{}] = {} > [{}] = {}", i, h.0[i], j1, h.0[j1]);
            verify(h, j1);
        }
        if j2 < n {
            assert!(!h.less(j2, i), "heap invariant invalidated [{}] = {} > [{}] = {}", i, h.0[i], j1, h.0[j2]);
            verify(h, j2);
        }
    }

    #[test]
    fn go_init0() {
        let h = vec![0; 20];
        let mut h = HeapType::new(MinHeap(h));
        verify(&h.data, 0);

        let mut i = 1;
        while h.len() > 0 {
            let x = h.pop().unwrap();
            verify(&h.data, 0);
            assert_eq!(x, 0, "{}.th pop got {}; want {}", i, x, 0);
            i += 1;
        }
    }

    #[test]
    fn go_init1() {
        let mut h = vec![];
        for i in 1..=20 {
            h.push(i);
        }
        let mut h = HeapType::new(MinHeap(h));
        verify(&h.data, 0);

        let mut i = 1;
        while h.len() > 0 {
            let x = h.pop().unwrap();
            verify(&h.data, 0);
            assert_eq!(x, i, "{}.th pop got {}; want {}", i, x, i);
            i += 1;
        }
    }

    #[test]
    fn go_test() {
        let mut h = MinHeap(Vec::new());
        verify(&h, 0);
        for i in (11..=20).rev() {
            h.push(i);
        }
        let mut h = HeapType::new(h);
        verify(&h.data, 0);
        for i in (1..=10).rev() {
            h.push(i);
            verify(&h.data, 0);
        }

        let mut i = 1;
        while h.len() > 0 {
            let x = h.pop().unwrap();
            if i < 20 {
                h.push(20 + i);
            }
            verify(&h.data, 0);
            assert_eq!(x, i, "{}.th pop got {}; want {}", i, x, i);
            i += 1;
        }
    }

    #[test]
    fn go_test_remove0() {
        let mut h = HeapType::new(MinHeap(vec![]));
        for i in 0..10 {
            h.push(i);
        }
        verify(&h.data, 0);

        while h.len() > 0 {
            let i = h.len() - 1;
            let x = h.remove(i);
            assert_eq!(x, i as i32, "Remove({}) got {}; want {}", i, x, i);
            verify(&h.data, 0);
        }
    }

    #[test]
    fn go_test_remove1() {
        let mut h = HeapType::new(MinHeap(vec![]));
        for i in 0..10 {
            h.push(i);
        }
        verify(&h.data, 0);

        let mut i = 0;
        while h.len() > 0 {
            let x = h.remove(0);
            assert_eq!(x, i as i32, "Remove(0) got {}; want {}", x, i);
            verify(&h.data, 0);
            i += 1;
        }
    }

    #[test]
    fn go_test_remove2() {
        const N: i32 = 10;
        let mut h = HeapType::new(MinHeap(vec![]));
        for i in 0..N {
            h.push(i);
        }
        verify(&h.data, 0);

        let mut m = HashSet::new();
        while h.len() > 0 {
            m.insert(h.remove((h.len() - 1) / 2));
            verify(&h.data, 0);
        }
        assert_eq!(m.len(), N as usize, "len(m) = {}; want {}", m.len(), N);
        for i in 0..N {
            assert!(m.contains(&i), "m[{}] doesn't exist", i);
        }
    }

    #[test]
    fn go_test_fix() {
        let mut h = HeapType::new(MinHeap(vec![]));
        let mut i = 200;
        while i > 0 {
            h.push(i);
            i -= 10;
        }
        verify(&h.data, 0);

        assert_eq!(h.peak(), Some(&10), "Expected head to be 10, was {:?}", h.peak());
        h.data.0[0] = 210;
        h.fix(0);
        verify(&h.data, 0);

        let mut rng = thread_rng();
        for i in 0..100 {
            let elem = rng.gen_range(0..h.len());
            if i % 2 == 0 {
                h.data.0[elem] *= 2;
            } else {
                h.data.0[elem] /= 2;
            }
            h.fix(elem);
            verify(&h.data, 0);
        }
    }
}
