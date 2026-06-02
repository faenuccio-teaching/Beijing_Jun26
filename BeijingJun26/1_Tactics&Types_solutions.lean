import Mathlib.Tactic

variable (P Q R S : Prop)
open Polynomial

section Intro
open Classical Set


example (n : ℕ) (hn : n ≤ 3) : n ≤ 5 := by
  apply le_trans
  use hn
  norm_num
  -- linarith

example (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] (y : Y) :
    Continuous (fun x : X ↦ y) := by
  rw [continuous_def]
  intro U hU
  rw [preimage_const]
  split_ifs
  exact isOpen_univ
  exact isOpen_empty
  -- exact continuous_const

end Intro

-- `⌘`

/- # exact, intro, apply, rfl-/

-- Use of the `exact` tactic

example (hP : P) : P := by
  exact hP

-- Use of the `apply` tactic

example (h : P → Q) (hP : P) : Q := by
  apply h
  exact hP

-- Use of the `intro` tactic

example : P → P := by
  intro hP
  exact hP

-- Use `\.` to write `·`

example : (P → Q → R) → ((P → Q) → (P → R)) := by
  intro h1
  intro h2
  intro hP
  apply h1
  · exact hP
  · apply h2
    exact hP


-- Use of the `rfl` tactic

example : P = P := by
  rfl


example : 3 = 2 + 1 := by
  rfl

-- `⌘`

-- # `rw`

-- `P` is not a proposition: it is a True/False statement for terms in `α`.

example (α : Type) (P : α → Prop) (x y : α) (hx : P x) (h : y = x) : P y := by
  rw [h]
  exact hx



example (α : Type) (P Q : α → Prop) (x : α) (hP : P x) (h : P = Q) : Q x := by
  rw [← h] -- Use `\l` to write `←`
  exact hP


example (α : Type) (P Q : α → Prop) (x : α) (hP : P x) (h : P = Q) : Q x := by
  rw [h] at hP
  exact hP

-- `⌘`

/- # Conjunction / And
  Use `\and` to write `∧` -/


example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  · exact hP
  · exact hQ


example : P ∧ Q → P := by
  intro h
  exact h.left

/-  # Disjunction / Or
  Use `\or` to write `∨` -/


example : P → P ∨ Q := by
  intro hP
  left
  exact hP

/- Symmetry of `∨`, and use of `assumption`  -/
example : P ∨ Q → Q ∨ P := by
  intro h
  cases h
  · right
    assumption
  · left
    assumption

/- The result of `cases` can be given explicit names, by using `rcases h with h1 | h2 `-/
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h1 h2 h3
  rcases h1 with h | h
  · apply h2
    exact h
  · apply h3
    exact h

-- `⌘`

/- Use of the `by_cases` tactic: the law of excluded middle. -/
example : R ∨ ¬ R := by
  by_cases hR : R
  · left
    exact hR
  · right
    exact hR

example (h1 : P → Q) (h2 : ¬ P → R) : Q ∨ R := by
  by_cases hP : P
  · left
    apply h1
    exact hP
  · right
    apply h2
    exact hP

-- `⌘`

/- # Types -/

#check 2
#check ℕ
#check (2 : ℤ)
#check 2 < 3
#check (∀ n : ℕ, ∀ x y z : ℤ, 2 < n → x ^ n + y ^ n = z ^ n → x*y*z = 0)
#check Real.sin
#check (Real.sin : ℝ → ℝ)


example : (1 : ℕ) = (1 : ℝ) := by
  rfl


example : (1 : ℕ) = (1 : ℚ) := by
  rfl -- sometimes things look strange! We'll spend most of `Class 3` understanding what happens.


example : (1 : ℚ) = (1 : ℚ[X]):= by
  rfl

-- `⌘`

/- ## Prop types -/

#check 37 < 1
#check True
#check False
#check trivial
#check true
#check false
#check Bool


example : True := by
  exact trivial

example : true = True := by
  rfl

example : true = false → False := by
  intro h
  have H := Bool.eq_true_and_eq_false_self
  have H1 := H true
  rw [← H1]
  constructor
  rfl
  rw [h]

-- `⌘`

/- # Exercises -/

-- Modus Ponens: if `P → Q` then `Q` can be deduced from `P`
-- **Exercise**
example : P → (P → Q) → Q := by
  intro hP h
  apply h
  exact hP


-- Transitivity of `→`
-- **Exercise**
example : (P → Q) → (Q → R) → P → R := by
  intro h1 h2 hP
  apply h2
  apply h1
  exact hP

-- **Exercise**
example (hP : P) : Q → (hP = hP) := by
  intro
  rfl

-- **Exercise**
example (hP : P) : R → P → Q → (hP = hP) := by
  intro _ _ _
  rfl

-- **Exercise**
example (n : ℕ) (h : n = 5) : n = 2 + 3 := by
  rw [h]

-- **Exercise**
example (n m : ℕ) (hn : n = 5) (hm : 11 = m) : m = n + 6 := by
  rw [hn, ← hm]

-- **Exercise**
example (α : Type) (a b c : α) (H : (a = b) → P ) (h1 : c = a) (h2 : b = c) : P := by
  apply H
  rw [h2]
  rw [← h1]
  -- exact h2

-- **Exercise**
example : P ∧ Q → Q := by
  intro h
  exact h.2

-- **Exercise**
example : (P → Q → R) → P ∧ Q → R := by
  intro h1 h2
  apply h1
  · exact h2.1
  · exact h2.2

-- `∧` is symmetric
-- **Exercise**
example : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.right
  · exact h.1


-- `∧` is transitive
-- **Exercise**
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2
  constructor
  · exact h1.1
  · exact h2.2

-- **Exercise**
example : False → P ∨ False := by
  intro
  right
  assumption

-- **Exercise**
example : (P ∧ Q → R) → P → Q → R := by
  intro h hP hQ
  apply h
  constructor
  · exact hP
  · exact hQ

-- **Exercise**
example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ

-- **Exercise**
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1 h2 h3
  rcases h3 with h31 | h32
  · left
    exact h1 h31
  · right
    exact h2 h32


-- **Exercise**
example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h1 h2
  rcases h2 with h21 | h22
  · left
    exact h1 h21
  · right
    exact h22
