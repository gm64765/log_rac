import mathlib

inductive full_binary_tree : ℕ → Type
| leaf : full_binary_tree 0
| node {n : ℕ} (left : full_binary_tree n) (right : full_binary_tree (n - 1)) : full_binary_tree (n + 1)


inductive plane_tree : Type
| node : List plane_tree → plane_tree

open full_binary_tree
def num_nodes_full_binary_tree {n : ℕ} : full_binary_tree n → ℕ
| full_binary_tree.leaf => 1
| (full_binary_tree.node left right) => num_nodes_full_binary_tree left + num_nodes_full_binary_tree right + 1

def height_full_binary_tree {n : ℕ} : full_binary_tree n → ℕ
| full_binary_tree.leaf => 0
| (full_binary_tree.node left right) => max (height_full_binary_tree left) (height_full_binary_tree right) + 1


def plane_tree_to_full_binary_tree : plane_tree → Σ' (n : ℕ), full_binary_tree n
| (plane_tree.node []) => ⟨0, full_binary_tree.leaf⟩
| (plane_tree.node (T::l)) =>
  let ⟨n, IH_tree⟩ := plane_tree_to_full_binary_tree T;
  let right_n := n - 1;
  full_binary_tree.node IH_tree (nat.rec_on right_n full_binary_tree.leaf (λ _ , full_binary_tree.leaf))
