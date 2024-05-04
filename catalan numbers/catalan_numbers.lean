import mathlib
-- The type of full binary trees

inductive full_binary_tree : Type
| leaf : full_binary_tree
| node : (T₁ T₂ : full_binary_tree) → full_binary_tree

inductive plane_tree : Type
| node : List plane_tree → plane_tree


-- to naj bi delalo

def plane_tree_to_full_binary_tree : plane_tree → full_binary_tree -- to bi naj bilo pravilno
| (plane_tree.node []) => full_binary_tree.leaf
| (plane_tree.node (T::l)) => full_binary_tree.node (plane_tree_to_full_binary_tree T) (plane_tree_to_full_binary_tree (plane_tree.node l))
