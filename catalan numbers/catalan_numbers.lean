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




theorem gcd_consecutive (n : ℕ) : Nat.gcd n (n + 1) = 1 := by
  have h : Nat.gcd n (n + 1) = 1 := by
    simp [gcd]
  exact h

--theorem help2 (n : ℕ) : ((2 * n).factorial) / (n.factorial * (2 * n - n).factorial) = ((2 * n).factorial) / (n.factorial * n.factorial) := by
  --let m := ((2 * n).factorial) / (n.factorial * (2 * n - n).factorial)

  --have h : (2 * n - n) = n := by
    --rw [two_mul]
    --exact Nat.add_sub_cancel n n
  --rw [h]

theorem omg (n : ℕ) : n ≤ 2 * n := by
    rw [two_mul]
    exact Nat.le_add_left n n

--theorem see : ∀(n : ℕ) (h : n > 0), 2 * n - (n + 1) = n - 1 := by
  --intro n
  --rw [← add_left_inj]
  --rw [Nat.sub_add_cancel]
  --nth_rw 1 [← Nat.add_assoc]
  --rw [two_mul]
  --rw [← Nat.pred_eq_sub_one]
  --rw [Nat.add_assoc]
  --rw [Nat.add_one]
  --rw [Nat.add_succ]
  --rw [Nat.add_comm (Nat.pred n) n]
  --rw [← Nat.add_succ]
  --rw [Nat.succ_pred]
  --simp
  --exact h

--theorem prosim (n : ℕ) : (2 * n - (n + 1)).factorial = (2 * n - n).factorial / n := by


--theorem omg2 (n : ℕ) : n + 1 ≤ 2 * n := by
  --rw [two_mul]
  --rw [Nat.add_comm n 1]
  --have h : 2 * n = n + 1 + n - 1 := by
    --rw [two_mul]


--theorem div_by_n_plus_one (n : ℕ) : (n + 1) ∣ (Nat.choose (2 * n) (n)) := by

  --have def_binom : (2 * n).choose n = ((2 * n).factorial) / (n.factorial * n.factorial) := by
    --rw [Nat.choose_eq_factorial_div_factorial]
    --rw [help2]
    --apply omg

  --have help : (2 * n).choose (n + 1) = (2 * n).choose n * (2 * n - n) / (n + 1) := by
    --rw [Nat.choose_eq_factorial_div_factorial]
    --rw [Nat.factorial_succ]

--theorem prosim_bog_uslisi_me (n : ℕ) : (2 * n).choose (n + 1) = n * (2 * n).choose n / (n + 1) := by
--rw [Nat.choose_eq_factorial_div_factorial]

--helper function for 2 (n + 1) - n + 1 = n + 2
theorem  pomoc1 : ∀ (n : ℕ), 2 * Nat.succ n - Nat.succ n + 1 = Nat.succ n + 1 := by
  intro n
  rw [Nat.two_mul]
  rw [Nat.add_sub_self_left]

--helper function for n = 2 (n + 1) - (n + 2)
theorem pomoc2 : ∀ (n : ℕ), n = 2 * Nat.succ n - (Nat.succ n + 1) := by
  intro n
  rw [Nat.two_mul]
  nth_rw 2 [← Nat.add_one]
  nth_rw 1 [← Nat.add_assoc]
  nth_rw 2 [Nat.add_comm]
  nth_rw 1 [Nat.add_assoc]
  rw [Nat.add_sub_self_right (n) (Nat.succ n + 1)]

--helper function for n + 1 = 2 (n + 1) - (n + 1)
theorem pomoc3 : ∀ (n : ℕ), Nat.succ n = 2 * Nat.succ n - Nat.succ n := by
  intro n
  rw [Nat.two_mul]
  rw [Nat.add_sub_self_right]

--helper function for (n + 1) (2(n + 1) choose (n + 1) + 2(n + 1) choose (n + 1) = (n + 2) (2(n + 1) choose (n + 1))
theorem pomoc4 : ∀ (n : ℕ), Nat.succ n * Nat.choose (2 * Nat.succ n) (Nat.succ n) + Nat.choose (2 * Nat.succ n) (Nat.succ n) = (Nat.succ n + 1) * Nat.choose (2 * Nat.succ n) (Nat.succ n) := by
  intro n
  nth_rw 2 [← Nat.one_mul (Nat.choose (2 * Nat.succ n) (Nat.succ n))]
  rw [← Nat.right_distrib]

--helper function for (n + 1)! = (2 * (n + 1) - (n + 1))!
theorem pomoc5 : ∀ (n : ℕ), n + 1 = 2 * (n + 1) - (n + 1) := by
  intro n
  rw [← add_left_inj]
  rw [Nat.sub_add_cancel]
  nth_rw 1 [← Nat.add_assoc]
  ring
  linarith

--helper function for n! = (2 * (n + 1) - (n + 2))!
theorem pomoc6 : ∀ (n : ℕ), n  = 2 * (n + 1) - (n + 1 + 1) := by
  intro n
  rw [← add_left_inj]
  rw [Nat.sub_add_cancel]
  nth_rw 1 [← Nat.add_assoc]
  ring
  linarith

-- first we rewrite 2n choose n, after rewriting the solution is a consequence
theorem rewrite_2n (n : ℕ) : Nat.choose (2 * n) n = (n + 1) * (Nat.choose (2 * n) n - Nat.choose (2 * n) (n + 1)) := by
  cases n with
  | zero => -- the case where n = 0
    rw [Nat.choose_zero_right]
    rw [Nat.zero_add]
    rw [one_mul]
    rw [Nat.choose_one_right]
  | succ n => -- induction step
  rw [Nat.mul_sub_left_distrib]
  rw [Nat.right_distrib]
  rw [Nat.one_mul]
  nth_rw 3 [Nat.add_comm]
  apply Eq.symm
  -- add 2n choose (n+1) to both sides, they cancel out
  -- using tactic Nat.sub_add_cancel, later prove m ≤ n
  rw [← add_left_inj]
  rw [Nat.sub_add_cancel]
  nth_rw 1 [Nat.add_comm]
  rw [add_right_inj]
  nth_rw 3 [Nat.mul_comm]
  -- multiply both sides of equation by (n+1)! and (n)!
  -- they have to be positive (obviously)
  have h : 0 < Nat.factorial (n + 1) * Nat.factorial (n) := by
    apply Nat.mul_pos
    exact Nat.factorial_pos (n + 1)
    exact Nat.factorial_pos n
  -- multiply
  apply Nat.eq_of_mul_eq_mul_right h
  -- use tactic Nat.choose_mul_factorial_mul_factorial to cancel things out
  nth_rw 4 [Nat.mul_comm]
  nth_rw 1 [Nat.mul_assoc]
  nth_rw 2 [← Nat.mul_assoc]
  nth_rw 2 [← Nat.mul_assoc]
  nth_rw 3 [Nat.mul_comm]
  nth_rw 1 [← Nat.mul_assoc]
  nth_rw 1 [← Nat.mul_assoc]

  rw [← Nat.factorial_succ]
  nth_rw 1 [Nat.mul_assoc]
  nth_rw 1 [← Nat.mul_assoc]
  nth_rw 5 [Nat.succ_eq_add_one]
  nth_rw 3 [Nat.mul_assoc]

  rw [← Nat.factorial_succ (n + 1)]
  nth_rw 4 [pomoc5]
  nth_rw 4 [Nat.add_one]
  nth_rw 4 [Nat.add_one]
  rw [pomoc1]

  nth_rw 8 [pomoc2 n]

  nth_rw 4 [Nat.add_comm]
  nth_rw 5 [Nat.add_comm]
  rw [Nat.choose_mul_factorial_mul_factorial]
  rw [Nat.add_one]
  nth_rw 2 [Nat.mul_comm]
  nth_rw 4 [pomoc3]
  rw [Nat.choose_mul_factorial_mul_factorial]

  linarith
  linarith

  -- proving m ≤ n
  nth_rw 1 [← Nat.one_mul ((2 * (n + 1)).choose (n + 1))]
  rw [Nat.one_mul]
  nth_rw 2 [Nat.add_one]
  nth_rw 2 [Nat.add_one]
  rw [pomoc4]
  apply Nat.mul_le_mul_left
-- proving inequality
  have h : (2 * (Nat.succ n)).choose (Nat.succ n + 1) * (Nat.factorial (Nat.succ n + 1) * Nat.factorial (Nat.succ n)) ≤ (2 * (Nat.succ n)).choose (Nat.succ n) *  (Nat.factorial (Nat.succ n + 1) * Nat.factorial (Nat.succ n)) := by
    -- removing choose from lhs
    nth_rw 2 [Nat.factorial_succ]
    nth_rw 1 [← Nat.mul_assoc]
    nth_rw 4 [Nat.mul_comm]
    nth_rw 1 [← Nat.mul_assoc]
    nth_rw 4 [pomoc6 n]
    rw [Nat.choose_mul_factorial_mul_factorial]
    -- removing choose from rhs
    nth_rw 1 [Nat.factorial_succ]
    nth_rw 6 [Nat.mul_comm]
    nth_rw 1 [Nat.mul_assoc]
    nth_rw 6 [Nat.mul_comm]
    nth_rw 2 [← Nat.mul_assoc]
    nth_rw 1 [← Nat.mul_assoc]
    nth_rw 1 [← Nat.mul_assoc]
    rw [Nat.add_one]
    nth_rw 6 [pomoc3]
    rw [Nat.choose_mul_factorial_mul_factorial]

    linarith
    linarith
    linarith
--this is it, just tell lean factorials are positive
  nth_rw 1 [Nat.add_comm]
  apply le_of_mul_le_mul_right h
  apply Nat.mul_pos
  exact Nat.factorial_pos (n + 1 + 1)
  exact Nat.factorial_pos (n + 1)


-- applying the theorem
theorem divisibility_by_n_plus_one (n : ℕ) : (n + 1) ∣ Nat.choose (2 * n) n := by
  rw [rewrite_2n]
  apply dvd_mul_right
