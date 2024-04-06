use std::cmp::Ordering;

/// A basic implementation of a binary search tree. Does not implement self-balancing or sharing subtrees with multiples parents.
pub struct Tree<T: Ord>(Option<Box<TreeNode<T>>>);

struct TreeNode<T: Ord> {
    val: T,
    left: Tree<T>,
    right: Tree<T>,
}

impl<T: Ord> TreeNode<T> {
    fn max(&self) -> &T {
        match &self.right.0 {
            None => &self.val,
            Some(right) => right.max(),
        }
    }

    fn min(&self) -> &T {
        match &self.left.0 {
            None => &self.val,
            Some(left) => left.min(),
        }
    }
}

impl<T: Ord> Tree<T> {
    /// Constructs an empty tree.
    pub fn empty() -> Self {
        Tree(None)
    }

    /// Constructs a tree containing the single value given.
    pub fn singleton(val: T) -> Self {
        Tree(Some(Box::new(TreeNode {
            val,
            left: Tree::empty(),
            right: Tree::empty(),
        })))
    }

    /// Checks if the tree is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut tree = binary_tree::Tree::empty();
    /// assert!(tree.is_empty());
    ///
    /// tree.insert(5);
    /// assert!(!tree.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        matches!(self, Tree(None))
    }

    pub fn len(&self) -> usize {
        match &self.0 {
            None => 0,
            Some(tree_node) => 1 + tree_node.left.len() + tree_node.right.len(),
        }
    }

    /// Checks if the tree contains the value when given a reference
    /// to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut tree = binary_tree::Tree::empty();
    /// assert!(!tree.contains(&10));
    ///
    /// tree.insert(10);
    /// assert!(tree.contains(&10));
    /// ```
    pub fn contains(&self, val: &T) -> bool {
        match &self.0 {
            None => false,
            Some(tree_node) => match tree_node.val.cmp(val) {
                Ordering::Equal => true,
                Ordering::Less => tree_node.right.contains(val),
                Ordering::Greater => tree_node.left.contains(val),
            },
        }
    }

    /// Inserts the given value into the tree.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut tree = binary_tree::Tree::empty();
    /// tree.insert(10);
    /// assert!(tree.contains(&10));
    /// ```
    pub fn insert(&mut self, val: T) {
        match &mut self.0 {
            None => *self = Tree::singleton(val),
            Some(tree_node) => match tree_node.val.cmp(&val) {
                Ordering::Greater => tree_node.left.insert(val),
                Ordering::Less => tree_node.right.insert(val),
                Ordering::Equal => (),
            },
        }
    }

    /// Returns a reference to the maximum value in the tree, or `None` if
    /// the tree is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// let vec = Vec::from([3, 6, 8, 1, 2, 5]);
    /// let tree = binary_tree::Tree::from_vec(vec);
    /// assert_eq!(tree.max(), Some(&8));
    /// ```
    ///
    /// ```
    /// let tree: binary_tree::Tree<i32> = binary_tree::Tree::empty();
    /// assert_eq!(tree.max(), None);
    /// ```
    pub fn max(&self) -> Option<&T> {
        self.0.as_ref().map(|tree_node| tree_node.max())
    }

    /// Returns a reference to the minimum value in the tree, or `None` if
    /// the tree is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// let vec = Vec::from([3, 6, 8, 1, 2, 5]);
    /// let tree = binary_tree::Tree::from_vec(vec);
    /// assert_eq!(tree.min(), Some(&1));
    /// ```
    ///
    /// ```
    /// let tree: binary_tree::Tree<i32> = binary_tree::Tree::empty();
    /// assert_eq!(tree.min(), None);
    /// ```
    pub fn min(&self) -> Option<&T> {
        self.0.as_ref().map(|tree_node| tree_node.min())
    }

    /// Removes the maximum value from the tree and returns it, or `None` if
    /// the tree is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// let vec = Vec::from([3, 6, 8, 1, 2, 5]);
    /// let mut tree = binary_tree::Tree::from_vec(vec);
    /// assert_eq!(tree.pop_max(), Some(8));
    /// assert!(!tree.contains(&8));
    /// ```
    ///
    /// ```
    /// let mut tree: binary_tree::Tree<i32> = binary_tree::Tree::empty();
    /// assert_eq!(tree.pop_max(), None);
    /// ```
    pub fn pop_max(&mut self) -> Option<T> {
        let tree_node = self.0.as_mut()?;

        if tree_node.right.is_empty() {
            let TreeNode { val, left, .. } = *self.0.take()?;
            self.0 = left.0;

            Some(val)
        } else {
            tree_node.right.pop_max()
        }
    }

    /// Removes the minimum value from the tree and returns it, or `None` if
    /// the tree is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// let vec = Vec::from([3, 6, 8, 1, 2, 5]);
    /// let mut tree = binary_tree::Tree::from_vec(vec);
    /// assert_eq!(tree.pop_min(), Some(1));
    /// assert!(!tree.contains(&1));
    /// ```
    ///
    /// ```
    /// let mut tree: binary_tree::Tree<i32> = binary_tree::Tree::empty();
    /// assert_eq!(tree.pop_min(), None);
    /// ```
    pub fn pop_min(&mut self) -> Option<T> {
        let tree_node = self.0.as_mut()?;

        if tree_node.left.is_empty() {
            let TreeNode { val, right, .. } = *self.0.take()?;
            self.0 = right.0;

            Some(val)
        } else {
            tree_node.left.pop_min()
        }
    }

    /// Deletes a value from the tree when given a reference to that value.
    ///
    /// # Examples
    ///
    /// ```
    /// let vec = Vec::from([3, 6, 8, 1, 2, 5]);
    /// let mut tree = binary_tree::Tree::from_vec(vec);
    /// assert!(tree.contains(&3));
    ///
    /// tree.delete(&3);
    /// assert!(!tree.contains(&3));
    /// ```
    pub fn delete(&mut self, val: &T) {
        if let Some(tree_node) = &mut self.0 {
            match tree_node.val.cmp(val) {
                Ordering::Greater => tree_node.left.delete(val),
                Ordering::Less => tree_node.right.delete(val),
                Ordering::Equal => {
                    if let Some(val) = tree_node.left.pop_max() {
                        tree_node.val = val
                    } else if let Some(val) = tree_node.right.pop_min() {
                        tree_node.val = val
                    } else {
                        self.0 = None
                    }
                }
            }
        }
    }

    /// Returns an iterator yielding references to the value in the tree
    /// in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = Vec::from([3, 6, 8, 1, 2, 5]);
    /// let tree = binary_tree::Tree::from_vec(vec.clone());
    ///
    /// vec.sort();
    /// let vec_from_tree: Vec<i32>
    ///     = tree.iter().cloned().collect();
    ///
    /// assert_eq!(vec, vec_from_tree);
    /// ```
    pub fn iter(&self) -> BSTIter<T> {
        BSTIter {
            stack: Vec::from([BSTIterAction::Explore(self)]),
            order: BSTIterOrder::Inorder,
        }
    }

    /// Returns an iterator yielding references to the values in the tree
    /// in post-order.
    pub fn postorder_iter(&self) -> BSTIter<T> {
        BSTIter {
            stack: Vec::from([BSTIterAction::Explore(self)]),
            order: BSTIterOrder::Postorder,
        }
    }

    /// Returns an iterator yielding references to the values in the tree
    /// in pre-order.
    pub fn preorder_iter(&self) -> BSTIter<T> {
        BSTIter {
            stack: Vec::from([BSTIterAction::Explore(self)]),
            order: BSTIterOrder::Preorder,
        }
    }

    /// Constructs a tree given a vector of values.
    ///
    /// # Examples
    ///
    /// ```
    /// let vec = Vec::from([5, 2, 10, 3, 2, 1, -4]);
    /// let tree = binary_tree::Tree::from_vec(vec.clone());
    ///
    /// for item in vec {
    ///     assert!(tree.contains(&item));
    /// }
    /// ```
    pub fn from_vec(vec: Vec<T>) -> Self {
        vec.into_iter().collect()
    }
}

impl<A: Ord> FromIterator<A> for Tree<A> {
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        iter.into_iter().fold(Tree(None), |mut tree, val| {
            tree.insert(val);
            tree
        })
    }
}

/// Binary search tree iterator. Supports pre-order, post-order and in-order traversal of the binary tree
///
/// This struct is created by the `iter`, `preorder_iter` and `postorder_iter` method on [`Tree`].
pub struct BSTIter<'a, A: Ord> {
    stack: Vec<BSTIterAction<'a, A>>,
    order: BSTIterOrder,
}

enum BSTIterAction<'a, A: Ord> {
    Yield(&'a A),
    Explore(&'a Tree<A>),
}

enum BSTIterOrder {
    Preorder,
    Postorder,
    Inorder,
}

impl<'a, A: Ord> Iterator for BSTIter<'a, A> {
    type Item = &'a A;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(action) = self.stack.pop() {
            match action {
                BSTIterAction::Yield(val) => return Some(val),
                BSTIterAction::Explore(tree) => {
                    if let Some(tree_node) = &tree.0 {
                        self.enqueue(tree_node)
                    }
                }
            }
        }

        None
    }
}

impl<'a, A: Ord> BSTIter<'a, A> {
    fn enqueue(&mut self, tree_node: &'a TreeNode<A>) {
        match self.order {
            BSTIterOrder::Preorder => {
                self.stack.push(BSTIterAction::Explore(&tree_node.right));
                self.stack.push(BSTIterAction::Explore(&tree_node.left));
                self.stack.push(BSTIterAction::Yield(&tree_node.val));
            }
            BSTIterOrder::Postorder => {
                self.stack.push(BSTIterAction::Yield(&tree_node.val));
                self.stack.push(BSTIterAction::Explore(&tree_node.right));
                self.stack.push(BSTIterAction::Explore(&tree_node.left));
            }
            BSTIterOrder::Inorder => {
                self.stack.push(BSTIterAction::Explore(&tree_node.right));
                self.stack.push(BSTIterAction::Yield(&tree_node.val));
                self.stack.push(BSTIterAction::Explore(&tree_node.left));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn from_vec_contains_all_vec_elements(
            vec in proptest::collection::vec(-1000..1000, 0..100)
        ) {
            let tree = Tree::from_vec(vec.clone());
            prop_assert!(vec.iter().all(|num| tree.contains(num)));
        }

        #[test]
        fn inorder_returns_elements_in_correct_order(
            mut vec in proptest::collection::vec(-1000..1000, 0..100)
        ) {
            let tree = Tree::from_vec(vec.clone());

            vec.sort();
            vec.dedup();

            let tree_inorder_vec: Vec<i32>
                = tree.iter().cloned().collect();

            prop_assert_eq!(tree_inorder_vec, vec);
        }

        #[test]
        fn max(
            vec in proptest::collection::vec(-1000..1000, 0..100)
        ) {
            let tree = Tree::from_vec(vec.clone());
            prop_assert_eq!(tree.max(), vec.iter().max());
        }

        #[test]
        fn min(
            vec in proptest::collection::vec(-1000..1000, 0..100)
        ) {
            let tree = Tree::from_vec(vec.clone());
            prop_assert_eq!(tree.min(), vec.iter().min());
        }

        #[test]
        fn popmax(
            vec in proptest::collection::vec(-1000..1000, 0..100)
        ) {
            let mut tree = Tree::from_vec(vec.clone());
            let tree_max = tree.pop_max();
            let vec_max = vec.iter().cloned().max();

            prop_assert_eq!(tree_max, vec_max);

            if let Some(val) = tree_max {
                prop_assert!(!tree.contains(&val));
            };
        }

        #[test]
        fn popmin(
            vec in proptest::collection::vec(-1000..1000, 0..100)
        ) {
            let mut tree = Tree::from_vec(vec.clone());
            let tree_min = tree.pop_min();
            let vec_min = vec.iter().cloned().min();

            prop_assert_eq!(tree_min, vec_min);

            if let Some(val) = tree_min {
                prop_assert!(!tree.contains(&val));
            };
        }

        #[test]
        fn insertion(
            n in -1000..1000i32,
            vec in proptest::collection::vec(-1000..1000, 0..100)
        ) {
            let mut tree = Tree::from_vec(vec);
            tree.insert(n);
            prop_assert!(tree.contains(&n));
        }

        #[test]
        fn insertion_then_deletion(n in -1000..1000i32,  vec in proptest::collection::vec(-1000..1000, 0..100)) {
            let mut tree = Tree::from_vec(vec);
            tree.insert(n);
            tree.delete(&n);
            prop_assert!(!tree.contains(&n));
        }

        #[test]
        fn double_insertion_then_deletion(n in -1000..1000i32,  vec in proptest::collection::vec(-1000..1000, 0..100)) {
            let mut tree = Tree::from_vec(vec);
            tree.insert(n);
            tree.insert(n);
            tree.delete(&n);
            prop_assert!(!tree.contains(&n));
        }
    }
}
