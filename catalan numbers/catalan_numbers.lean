import Init.Control.Basic
import mathlib
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
import MIL.Common

--import data.bool.basic


--import data.list.basic

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)


open BigOperators
open Finset
-- The type of full binary trees

-- SMALL TASKS
-- 1.  recursive definition
def catalan_n : ℕ → ℕ
 | 0 => 1
 | (n + 1) => Finset.univ.sum (λ (i : Fin n.succ) => catalan_n ↑i * catalan_n (n - ↑i))

#eval catalan_n 2

inductive Catalan : ℕ → Type
| zero : Catalan 0
| succ {n : ℕ}: Catalan n → Catalan (n + 1) → Catalan (n + 2)

open Catalan

--instance : Π {n : ℕ}, Repr (Catalan n)
--| zero => "Catalan.zero"
--| (succ c1 c2) => "(Catalan.succ " ++ repr c1 ++ " " ++ repr c2 ++ ")"

--#eval Catalan 0

/-
def Catalan.calc : Π (n : ℕ), Catalan n
| 0 => zero
| 1 => succ zero zero --Catalan.zero
| (nat.succ (nat.succ n)) =>
  let c_n := Catalan.calc (nat.succ n)
  let c_succ_n := Catalan.calc n
  Catalan.succ c_succ_n c_n
-/
open Catalan

def calculate_cat : ℕ → ℤ
| 0 => 1
-- (n + 1) => Finset.univ.sum (λ (i : Fin n.succ) => catalan_n ↑i * catalan_n (n - ↑i))
| n + 1 => Finset.univ.sum (λ (i : Fin n.succ) => calculate_cat i * calculate_cat (n - i))

#eval calculate_cat 4


-- Define factorial function
def factorial : ℕ → ℕ
| 0 => 1
| (n + 1) => (n + 1) * factorial n

-- Define binomial coefficients
def choose (n k : ℕ) : ℕ :=
  (factorial n) / ((factorial k) * (factorial (n - k)))


theorem fac_pos (n : ℕ) : 0 < (factorial n) := by
  induction' n with n ih
  · rw [factorial]
    exact zero_lt_one
  rw [factorial]
  exact mul_pos n.succ_pos ih



-- Lemma: Factorial is even for n > 0
theorem factorial_even (n : ℕ) (h : n > 10) : (factorial n) % 2 = 0 := by
  induction' n with d hd
  · rw[h]
    rw[factorial]
    linarith

  --{ cases (lt_irrefl 0 h) },
  --{ cases d,
  --  { refl },
  --  { rw nat.dvd_iff_mod_eq_zero,
  --    rw nat.mul_mod,
  --    exact hd (nat.succ_pos d) } }



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

-- 5. type of ballot sequences of length n (consisting of 1 and -1)
--def atom : Type :=
--|one
--|minus_one

inductive vote
| A
| B

open vote

def isEqual : vote → vote → Bool
| A, A => true
| B, B => true
| _, _ => false


--inductive plane_tree : Type
--|-- node : List plane_tree → plane_tree

--i--nductive full_binary_tree : Type
--| leaf : full_binary_tree
--| node : (T₁ T₂ : full_binary_tree) → full_binary_tree


--def example_sequence2 : vote_list := [A, B, A]
/-
def count_elements : List vote → vote → ℕ → ℕ
| [], _, acc => acc
| (x :: xs), v, acc => let res := (isEqual x v) ; if res then count_elements xs v (acc+1) else count_elements xs v acc
--count_elements xs v (acc + 1) else count_elements xs v acc
def reverse_list : List vote → List vote
| [] => []
| (x :: xs) => reverse_list xs ++ [x]

-- Example usage
#eval count_elements [A, B, A, A, B, B] A 0  -- should return 3
#eval count_elements [B, A, A, B, B] B 0  -- should return 3

-- Function to check if a sequence is a valid ballot sequence
def is_ballot_sequence_check : List vote → Bool
| [] => true
| (x::xs) =>
  let count_A := count_elements (x::xs) A 0
  let count_B := count_elements (x::xs) B 0
  if count_A < count_B then false
  else is_ballot_sequence_check xs

def is_ballot_sequence (l : List vote) : Bool :=
let lst := reverse_list l ;
is_ballot_sequence_check (lst)


#eval is_ballot_sequence [A, B, A, B, A, A]  -- should return true
#eval is_ballot_sequence [B, A, A, B, B]  -- should return false

-/

inductive vote_list : Type
| nil  : vote_list
| cons : vote → vote_list → vote_list

open vote_list

def example_sequence : vote_list := cons A (cons B (cons A (cons A (cons B nil))))

def count_elements : List vote → vote → ℕ → ℕ
| [], _, acc => acc
| (x :: xs), v, acc => let res := (isEqual x v) ; if res then count_elements xs v (acc+1) else count_elements xs v acc

def reverse_list : vote_list → List vote
| nil => []
| (vote_list.cons x xs) => reverse_list xs ++ [x]

 -- should return 3

-- Function to check if a sequence is a valid ballot sequence
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

-- 3rd exercise:
-- full binary trees_to_catalan_numbers
--def catalan_numbers : Type
--| catalan n



--def full_binary_trees_to_catalan_num : full_binary_tree → catalan_n
--  |
--  |
