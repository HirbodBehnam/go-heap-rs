# go-heap-rs
[![Test](https://github.com/HirbodBehnam/go-heap-rs/actions/workflows/test.yml/badge.svg)](https://github.com/HirbodBehnam/go-heap-rs/actions/workflows/test.yml)
[![Docs](https://docs.rs/go-heap-rs/badge.svg)](https://docs.rs/go-heap-rs/)

Golang's heap written in Rust

## Advantages
* More control over swap method
* Added `fix` and `remove` methods
* Full access to underlying data

## Disadvantages
* Must be manually backed by a collection like Vector
* Not really easy to work with
* Lack of some methods like `from`

## Importing

```toml
[dependencies]
go-heap-rs = "0.1"
```

## Example of usage
```rust
struct MinHeap<T: Ord>(Vec<T>);

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

fn test() {
    let my_vec = MinHeap(vec![2, 4, 3, 1]);
    let mut heap = HeapType::new(my_vec);
    assert_eq!(heap.peak(), Some(&1));
    assert_eq!(heap.pop(), Some(1));
    heap.push(-1);
    assert_eq!(heap.pop(), Some(-1));
}
```