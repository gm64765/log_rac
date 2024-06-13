--import Init.Control.Basic
--import Init.Data.Nat.Basic --  tocno ta
import Init
import Mathlib
import Mathlib.Data.Nat.Defs
import Mathlib.Algebra.Group.Basic

--import Mathlib.Data.Nat.GCD.Basic
--import Mathlib.Algebra.BigOperators.Basic
--import Mathlib.Data.Finset.Basic
--import MIL.Common
--import Mathlib.Data.Fintype.Basic --od tod dol
--import Mathlib.Data.Real.Basic
--import Mathlib.Data.Nat.Defs


variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)


open BigOperators
open Finset

/-
  =============================================================
  SMALL TASK 1
  =============================================================
  Recursive definition of Catalan numbers
-/

-- Inductive definition of Catalan numbers

inductive Catalan : ℕ → Type
| zero : Catalan 0
| succ {n : ℕ}: Catalan n → Catalan (n + 1) → Catalan (n + 2)

-- Another definition of Catalan numbers.
def catalan_number_n : ℕ → ℕ
| 0 => 1
| n + 1 => Finset.univ.sum (λ (i : Fin n.succ) => catalan_number_n i * catalan_number_n (n - i))

#eval catalan_number_n 4

/-
  =============================================================
  SMALL TASK 2
  =============================================================
  Formalising a concept of plane trees
-/

inductive plane_tree : Type
| node : List plane_tree → plane_tree

/-
  =============================================================
  SMALL TASK 3
  =============================================================
  Formalising a concept of full binary trees
-/

inductive full_binary_tree : Type
| leaf : full_binary_tree
| node : (T₁ T₂ : full_binary_tree) → full_binary_tree

/-
  =============================================================
  SMALL TASK 4
  =============================================================
  Formalising a concept of full binary trees with n nodes
-/

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


/-
  =============================================================
  SMALL TASK 5
  =============================================================
  Formalising a concept of ballot sequences of length n (consisting of A and B; there must be more of A votes)
-/

inductive vote
| A
| B

open vote

def isEqual : vote → vote → Bool
| A, A => true
| B, B => true
| _, _ => false

inductive vote_list : Type
| nil  : vote_list
| cons : vote → vote_list → vote_list

open vote_list

def example_sequence : vote_list := cons A (cons B (cons A (cons A (cons B nil))))

-- Helper function
def count_elements : List vote → vote → ℕ → ℕ
| [], _, acc => acc
| (x :: xs), v, acc => let res := (isEqual x v) ; if res then count_elements xs v (acc+1) else count_elements xs v acc

-- Helper function
def reverse_list : vote_list → List vote
| nil => []
| (vote_list.cons x xs) => reverse_list xs ++ [x]


-- Function checks if a sequence is a valid ballot sequence
-- All lists that satisfy this function are ballot sequences
def is_ballot_sequence_check : List vote → Bool
| [] => true
| (x::xs) =>
  let count_A := count_elements (x::xs) A 0
  let count_B := count_elements (x::xs) B 0
  if count_A < count_B then false
  else is_ballot_sequence_check xs

def is_ballot_sequence (l : vote_list) : Bool :=
let lst := reverse_list l ;
is_ballot_sequence_check (lst)

#eval is_ballot_sequence (cons A (cons B (cons A (cons A (cons B nil))))) -- should return true
#eval is_ballot_sequence (cons A (cons B (cons A (cons B (cons B nil)))))  -- should return false


/-
  ======================================================================
  LARGER TASK
  =====================================================================
  Larger task 4: Isomorphism between plane trees and list plane trees

-/


open plane_tree

-- Definitions of 2 mappings.
def list_to_plane_tree : List plane_tree → plane_tree
| n => plane_tree.node n

def plane_tree_to_list : plane_tree → List plane_tree
| plane_tree.node l => l

-- For both mappings we must show that they are inverses of each other.
theorem list_to_plane_inverse (lt : List plane_tree): plane_tree_to_list (list_to_plane_tree lt) = lt := by
rfl

theorem plane_list_inverse (pt : plane_tree) : list_to_plane_tree (plane_tree_to_list pt) = pt := by
cases pt with
| node n => simp [plane_tree_to_list, list_to_plane_tree]

-- Proof of bijection
theorem bijection :
∃ (f : List plane_tree → plane_tree) (g : plane_tree → List plane_tree), (∀ lt, g (f lt) = lt) ∧ (∀ n, f (g n) = n) :=
⟨list_to_plane_tree, plane_tree_to_list, list_to_plane_inverse, plane_list_inverse⟩




open plane_tree
open full_binary_tree


/-
  ======================================================================
  LARGER TASK 5
  =====================================================================
 We must prove Isomorphism between plane trees and full binary trees
 The task is unfinished
-/


-- We define 2 mappings
def plane_tree_to_full_binary_tree : plane_tree → full_binary_tree
| (plane_tree.node []) => full_binary_tree.leaf
| (plane_tree.node (T::l)) =>
  full_binary_tree.node (plane_tree_to_full_binary_tree T) (plane_tree_to_full_binary_tree (plane_tree.node l))


def full_binary_tree_to_plane_tree : full_binary_tree → plane_tree
| full_binary_tree.leaf => plane_tree.node []
| (full_binary_tree.node l r) =>
    match full_binary_tree_to_plane_tree r with
    | plane_tree.node ts => plane_tree.node (full_binary_tree_to_plane_tree l :: ts)


-- For both mappings we must show that they are inverses of each other.
theorem plane_to_full_inverse : ∀ (t : plane_tree), full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree t) = t := by
  intro t
  --induction t with -- Tried induction, did not finish
  cases t with
  | node ts =>
      cases ts with
      | nil => rfl --- For simple case it is simple
      | cons hd tl =>
        unfold plane_tree_to_full_binary_tree
        unfold full_binary_tree_to_plane_tree
        sorry

theorem full_to_plane_inverse : ∀ (t : full_binary_tree), plane_tree_to_full_binary_tree (full_binary_tree_to_plane_tree t) = t := by
  intro t
  induction t with -- Tried induction, did not finish
  | leaf => rfl -- For base case it is simple
  | node l r ih_l ih_r => sorry
