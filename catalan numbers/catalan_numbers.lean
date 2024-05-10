import mathlib


-- Small task 2: concept of plane trees
inductive plane_tree : Type
| node : List plane_tree → plane_tree

-- Small task 3: concept of full binary trees
inductive full_binary_tree : Type
| leaf : full_binary_tree
| node : (T₁ T₂ : full_binary_tree) → full_binary_tree

--Small task 4: concept of full binary trees with n nodes
inductive full_binary_tree_n : ℕ → Type
| leaf : full_binary_tree_n 0
| node {n : ℕ} (left : full_binary_tree_n n) (right : full_binary_tree_n (n - 1)) : full_binary_tree_n (n + 1)


open full_binary_tree_n

-- Number of nodes in full binary tree
def num_nodes_full_binary_tree {n : ℕ} : full_binary_tree_n n → ℕ
| full_binary_tree_n.leaf => 1
| (full_binary_tree_n.node left right) => num_nodes_full_binary_tree left + num_nodes_full_binary_tree right + 1

-- Height of full binary tree
def height_full_binary_tree {n : ℕ} : full_binary_tree_n n → ℕ
| full_binary_tree_n.leaf => 0
| (full_binary_tree_n.node left right) => max (height_full_binary_tree left) (height_full_binary_tree right) + 1

-- Larger task 4: Isomorphism between plane trees and full binary trees
def plane_tree_to_full_binary_tree : plane_tree → full_binary_tree
| (plane_tree.node []) => full_binary_tree.leaf
| (plane_tree.node (T::l)) => full_binary_tree.node (plane_tree_to_full_binary_tree T) (plane_tree_to_full_binary_tree (plane_tree.node l))
