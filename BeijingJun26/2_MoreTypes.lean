import Mathlib.Tactic

variable (P Q R S : Prop)
-- # More on Types

section DependentTypes

-- ## The hierarchy
#check ℕ
#check Type
#check Prop

-- `⌘`

-- ## Dependent types

#check λ n : ℕ ↦ 3 * n
#check fun n : ℕ ↦ 3 * n
#check fun x : ℝ ↦ x + Complex.I
#check (fun x : ℝ ↦ x + Complex.I) (Real.pi)

-- `⌘`

#check ∀ n : ℕ, Vector ℝ n
#check Π n : ℕ, Vector ℝ n
#check (n : ℕ) → Vector ℝ n
#check (λ n ↦ (0 : Vector ℝ n))

#check Σ n : ℕ, Vector ℝ n
#check (n : ℕ) × Vector ℝ n
#check (⟨3, (0 : Vector ℝ 3)⟩ : (n : ℕ) × Vector ℝ n)

#check ℕ → ℝ
#check Type 3 → Type 12
#check Type 3 → Prop -- Here `I : (Type 3 : Type 4) → (Prop : Type 0)` with `I α = Prop` for all `α`
#check Type 31 → False -- Here, `I : Type 31 → Prop`, with `I α = False` for all `α`

universe u v
variable {A : Sort u} (I : A → Sort v)


#check (a : A) → I a
#check Σ' (a : A), I a--(a : A), I a
#check (a : A) × I a--(a : A), I a

variable {A' : Type u} (J : A' → Type v)
#check (a : A') × J a

-- `⌘`

-- Euclid's proof, exhibiting the power of impredicativity
def Euclid_n : ℕ → Prop := fun n ↦ ∃ p, Nat.Prime p ∧ n < p
def Euclid_all : Prop := (n : ℕ) → (Euclid_n n)
def Euclid_forall : Prop := ∀ n, ∃ p, Nat.Prime p ∧ n < p
example : Euclid_all = Euclid_forall := sorry

theorem Euclid_all_proof : Euclid_all := by
  sorry

theorem exists_p_gt_100 (E : Euclid_forall) : ∃ p, Nat.Prime p ∧ 100 < p := by
  sorry


#check (∃ n : ℕ, n ^ 2 + 37 * n < 2 ^ n)

#check (a : ℕ) ×' ((fun n ↦ ∃ m : ℕ, n < m) a)
#check (⟨3,  ⟨42, by norm_num⟩⟩ : (a : ℕ) ×' ((fun n ↦ ∃ m : ℕ, n < m) a))

example (h : ∃ x : ℕ, 1 < x) : ℕ := by
  sorry

example (h : ∃ x : ℕ, 1 < x) : 1 < 2 := by
  sorry

example : ∃ x : ℝ, Real.sin x = 0 := by
  sorry

open Function in
example (f : ℝ → ℝ) (h : ∀ x, ∃ y, x = f y) : Surjective f := by
  sorry

-- `⌘`

/- # False, negation, contradiction -/

-- Use of the `exfalso` tactic
example : False → P := by
  sorry

-- type `¬` by typing `\not`.
-- **ToDo**
example : P → Q → P → ¬ Q → ¬ P := by
  sorry


-- Use of the `by_contra` tactic
-- **ToDo**
example : (¬Q → ¬P) → P → Q := by
  sorry


-- `⌘`

end DependentTypes


-- # : Inductive types
section InductiveTypes

inductive NiceType : Type
  | Tom : NiceType
  | Jerry : NiceType
  | f : NiceType → NiceType
  | g : ℕ → NiceType → NiceType → NiceType
open NiceType

#check NiceType
#check f (g 37 Tom Tom)
#check NiceType.rec

noncomputable
def F : NiceType → ℝ := by
  sorry

def Cat : NiceType := Tom

def Hunting : NiceType := g 2 Cat Jerry

-- #### Another example

inductive ENS_Or (p q : Prop) : Prop
| left : p → ENS_Or p q
| right : q → ENS_Or p q

#print ENS_Or

example (n : ℕ) : ENS_Or (n = 0) (∃ m, n = Nat.succ m) := by
  sorry

example (n : ℕ) : ENS_Or (n = 0) (∃ m, n = Nat.succ m) := by
  sorry


-- `⌘`

-- ## Many more examples

#print True
#print False
#print Bool
#print Nat
#print And
#print Equiv
#print Iff -- printed ↔

example : P ∧ (Q ∨ S) ↔ P ∧ Q ∨ P ∧ S := by
  sorry


-- `⌘`

end InductiveTypes

section Structures

inductive ENS_Nat
| ENS_zero : ENS_Nat
| ENS_succ : ENS_Nat → ENS_Nat
open ENS_Nat

#print ENS_Nat
#check ENS_Nat

def ENS_Nat_add : ENS_Nat → ENS_Nat → ENS_Nat := sorry

-- A structure containing simply a `0` and `+`:
#print AddZero

example : (AddZero ENS_Nat) := sorry



-- We want to prove that `ENS_Nat = ℕ`: after all they are *constructed* in the same way!
#print Equiv

def JustOne_fun : ℕ → ENS_Nat :=
  sorry


def JustOne_inv : ENS_Nat → ℕ :=
  sorry


-- The rest of the equivalence is left as an *exercise*.


end Structures


section Exercises
-- # Exercises

-- **Exercise**
-- What is the type of `¬`?

-- **Exercise**
-- Why is `¬ P : Prop` when `P : Prop`?


-- **Exercise**
/- Consider the function `F` sending `n : ℕ` to the statement
`0 ≠ n ∧ (∀ α : Type 2, ∃ v w : Vector α n), v ≠ w`
1. How do you expect `F 2` to look like?
2. What is the type of `fun n ↦ (fun (α : Type 2) ↦ Vector α n)`? To which universe level does this
  type belong to?
3. What is the type of `fun n ↦ ((fun α : Type 2) ↦ ∃ v : Vector α n, v ≠ 0`?
4. What is the type of `fun n ↦ (∀ α : Type 2, ∃ v : Vector α n, v ≠ 0)`? To which universe level
  does this type belong to?
5. What is the type of `F 2`, and to which universe level does this type belong?
6. Is `F 2` true?
7. What is the type of `F` and to which universe level does this type belong?
-/

variable (α : Type*) (p q : α → Prop) -- Use `\alpha` to write `α`

-- **Exercise**
example : True → True := by
  sorry


-- **Exercise**
example : (P → False) → P → Q := by
  sorry


-- **Exercise**
example : P → ¬ P → False := by
  sorry


-- **Exercise**
example : (P → ¬ Q) → (Q → ¬ P) := by
  sorry


-- **Exercise**
example (h : ¬ (2 = 2)) : P → Q := by
  sorry

-- **Exercise**
example : (∀ x : α, p x ∧ q x) → ∀ x : α, p x := by
  sorry

-- **Exercise**
example : (∀ x, p x ∨ R) ↔ (∀ x, p x) ∨ R := by
  sorry

-- **Exercise**
example (h : ∃ x, p x ∧ q x) : ∃ x, p x := by
  sorry

-- **Exercise**
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := by
  sorry

-- **Exercise**
example (a : α) : (∃ x, p x → R) ↔ ((∀ x, p x) → R) := by
  sorry

-- **Exercise**
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  sorry

-- **Exercise**
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  sorry

-- **Exercise**
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  sorry

-- **Exercise**
example : (∀ x, p x → R) ↔ (∃ x, p x) → R := by
  sorry

open Function


/- **Exercise**
In the following steps, you're required to complete the proof that `JustOne` is an equivalence
between `ENS_Nat` and `ℕ`. -/
open ENS_Nat


def JustOne_Left : LeftInverse JustOne_inv JustOne_fun := by
  intro n
  induction n with --I've pre-populated the structure, but if you type `induction n with`, Lean asks
  -- for the right fields
  | zero => sorry
  | succ m hm => sorry

def JustOne_Right : RightInverse JustOne_inv JustOne_fun := sorry


def JustOne : ℕ ≃ ENS_Nat := sorry


/- **Exercise**
The successor is not surjective, but you can't rely on the library because we're not using `ℕ`. -/
example : ¬ Surjective ENS_succ := by
  sorry


/- **Exercise**
   Define an inductive type `Politics` with two terms : `Right` and `Left`-/
inductive Politics
-- ???

-- leave this line as it is
open Politics

/- **Exercise**
Define a function `swap : Politics → Politics` sending `Right` to `Left` and viceversa-/
def swap : Politics → Politics := sorry

/- **Exercise**
State and prove that if someone is not on the `Right`, they are on the `Left` -/
-- example : ???

-- **Exercise**
-- Can you write down on paper, without using VSCode, the type of `Iff.rec`?

-- **Exercise**
-- Do you understand why the first of the next two lines compiles while the second
-- throws an error?
example (M : Type*) (α : Monoid M) : (1 : M) = (1 : M) := rfl
example (α : Type*) (M : Monoid α) : (1 : M) = (1 : M) := rfl

-- associativity of `∨`
-- **Exercise**
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  sorry


end Exercises
