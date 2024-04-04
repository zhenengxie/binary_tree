use std::cmp::Ordering;

pub struct Tree<T: Ord>(Option<Box<TreeNode<T>>>);

pub struct TreeNode<T: Ord> {
    val: T,
    left: Tree<T>,
    right: Tree<T>
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
    /// Constructs an empty tree
    pub fn empty() -> Self {
        Tree(None)
    }

    /// Constructs a tree containing the single value given
    pub fn singleton(val: T) -> Self {
        Tree(Some(Box::new(TreeNode{
            val,
            left: Tree::empty(),
            right: Tree::empty(),
        })))
    }

    /// Checks if the tree is empty
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
            Some(tree_node) => {
                1 + tree_node.left.len() + tree_node.right.len()
            }
        }
    }

    /// Checks if the tree contains the value when given a reference
    /// to the value
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
            }
        }
    }

    /// Inserts the given value into the tree
    pub fn insert(&mut self, val: T) {
        match &mut self.0 {
            None => *self = Tree::singleton(val),
            Some(tree_node) => match tree_node.val.cmp(&val) {
                Ordering::Greater => tree_node.left.insert(val),
                Ordering::Less => tree_node.right.insert(val),
                Ordering::Equal => (),
            }
        }
    }

    /// Returns a reference to the maximum value in the tree
    pub fn max(&self) -> Option<&T> {
        self.0.as_ref().map(|tree_node| tree_node.max())
    }

    /// Returns a reference to the minimum value in the tree
    pub fn min(&self) -> Option<&T> {
        self.0.as_ref().map(|tree_node| tree_node.min())
    }

    /// Returns and removes the maximum value of the tree
    pub fn pop_max(&mut self) -> Option<T> {
        let tree_node = self.0.as_mut()?;

        if tree_node.right.is_empty() {
            let TreeNode{val, left, ..} = *self.0.take()?;
            self.0 = left.0;

            Some(val)
        } else {
            tree_node.right.pop_max()
        }
    }

    /// Returns and removes the minimum value of the tree
    pub fn pop_min(&mut self) -> Option<T> {
        let tree_node = self.0.as_mut()?;

        if tree_node.left.is_empty() {
            let TreeNode{val, right, ..} = *self.0.take()?;
            self.0 = right.0;

            Some(val)
        } else {
            tree_node.left.pop_min()
        }
    }

    /// Deletes a given value from the tree
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

    /// Returns an iterator yielding references to the value in the tree in ascending order
    pub fn iter(&self) -> BSTIter<T> {
        BSTIter {
            stack: Vec::from([BSTIterAction::Explore(self)]),
            order: BSTIterOrder::Inorder
        }
    }

    /// Returns an iterator yielding references to the values in the tree
    /// in post-order
    pub fn postorder_iter(&self) -> BSTIter<T> {
        BSTIter {
            stack: Vec::from([BSTIterAction::Explore(self)]),
            order: BSTIterOrder::Postorder
        }
    }

    /// Returns an iterator yielding references to the values in the tree
    /// in pre-order
    pub fn preorder_iter(&self) -> BSTIter<T> {
        BSTIter {
            stack: Vec::from([BSTIterAction::Explore(self)]),
            order: BSTIterOrder::Preorder
        }
    }

    /// Constructs a tree given a vector of values
    pub fn from_vector(vec: Vec<T>) -> Self {
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
pub struct BSTIter<'a, A: Ord> {
    stack: Vec<BSTIterAction<'a, A>>,
    order: BSTIterOrder,
}

enum BSTIterAction<'a, A: Ord> {
    Yield(&'a A),
    Explore(&'a Tree<A>)
}

enum BSTIterOrder {
    Preorder,
    Postorder,
    Inorder
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
    fn enqueue (&mut self, tree_node: &'a TreeNode<A>) {
        match self.order {
            BSTIterOrder::Preorder => {
                self.stack.push(BSTIterAction::Explore(&tree_node.right));
                self.stack.push(BSTIterAction::Explore(&tree_node.left));
                self.stack.push(BSTIterAction::Yield(&tree_node.val));
            },
            BSTIterOrder::Postorder => {
                self.stack.push(BSTIterAction::Yield(&tree_node.val));
                self.stack.push(BSTIterAction::Explore(&tree_node.right));
                self.stack.push(BSTIterAction::Explore(&tree_node.left));
            },
            BSTIterOrder::Inorder => {
                self.stack.push(BSTIterAction::Explore(&tree_node.right));
                self.stack.push(BSTIterAction::Yield(&tree_node.val));
                self.stack.push(BSTIterAction::Explore(&tree_node.left));
            },
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
            let tree = Tree::from_vector(vec.clone());
            prop_assert!(vec.iter().all(|num| tree.contains(num)));
        }

        #[test]
        fn inorder_returns_elements_in_correct_order(
            vec in proptest::collection::vec(-1000..1000, 0..100)
        ) {
            let tree = Tree::from_vector(vec.clone());
            let mut sorted_vec = vec;
            sorted_vec.sort();
            sorted_vec.dedup();

            let tree_inorder_vec: Vec<i32>
                = tree.iter().cloned().collect();

            prop_assert_eq!(tree_inorder_vec, sorted_vec);
        }

        #[test]
        fn max(
            vec in proptest::collection::vec(-1000..1000, 0..100)
        ) {
            let tree = Tree::from_vector(vec.clone());
            prop_assert_eq!(tree.max(), vec.iter().max());
        }

        #[test]
        fn min(
            vec in proptest::collection::vec(-1000..1000, 0..100)
        ) {
            let tree = Tree::from_vector(vec.clone());
            prop_assert_eq!(tree.min(), vec.iter().min());
        }

        #[test]
        fn popmax(
            vec in proptest::collection::vec(-1000..1000, 0..100)
        ) {
            let mut tree = Tree::from_vector(vec.clone());
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
            let mut tree = Tree::from_vector(vec.clone());
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
            let mut tree = Tree::from_vector(vec);
            tree.insert(n);
            prop_assert!(tree.contains(&n));
        }

        #[test]
        fn insertion_then_deletion(n in -1000..1000i32,  vec in proptest::collection::vec(-1000..1000, 0..100)) {
            let mut tree = Tree::from_vector(vec);
            tree.insert(n);
            tree.delete(&n);
            prop_assert!(!tree.contains(&n));
        }

        #[test]
        fn double_insertion_then_deletion(n in -1000..1000i32,  vec in proptest::collection::vec(-1000..1000, 0..100)) {
            let mut tree = Tree::from_vector(vec);
            tree.insert(n);
            tree.insert(n);
            tree.delete(&n);
            prop_assert!(!tree.contains(&n));
        }
    }
}