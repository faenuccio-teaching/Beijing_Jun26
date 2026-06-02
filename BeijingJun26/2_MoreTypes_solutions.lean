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
example : Euclid_all = Euclid_forall := rfl

theorem Euclid_all_proof : Euclid_all := by
  intro n
  dsimp only [Euclid_n]
  sorry

theorem exists_p_gt_100 (E : Euclid_forall) : ∃ p, Nat.Prime p ∧ 100 < p := by
  specialize E 100
  exact E
  -- exact E 100


#check (∃ n : ℕ, n ^ 2 + 37 * n < 2 ^ n)

#check (a : ℕ) ×' ((fun n ↦ ∃ m : ℕ, n < m) a)
#check (⟨3,  ⟨42, by norm_num⟩⟩ : (a : ℕ) ×' ((fun n ↦ ∃ m : ℕ, n < m) a))

example (h : ∃ x : ℕ, 1 < x) : ℕ := by
  obtain ⟨n, hn⟩ := h

example (h : ∃ x : ℕ, 1 < x) : 1 < 2 := by
  obtain ⟨n, hn⟩ := h
  sorry

example : ∃ x : ℝ, Real.sin x = 0 := by
  use 0
  exact Real.sin_zero

open Function in
example (f : ℝ → ℝ) (h : ∀ x, ∃ y, x = f y) : Surjective f := by
  intro x
  obtain ⟨y, hy⟩ := h x
  use y
  exact hy.symm

-- `⌘`

/- # Negation and contradiction -/

-- Use of the `exfalso` tactic
example : False → P := by
  intro h
  exfalso
  exact h

-- type `¬` by typing `\not`.
example : P → Q → P → ¬ Q → ¬ P := by
  intro hp hq hp' h_neq abs
  apply h_neq
  exact hq

-- Use of the `by_contra` tactic
example : (¬Q → ¬P) → P → Q := by
  intro h1 hP
  by_contra h2
  have h3 := h1 h2
  exact h3 hP

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
  let G := NiceType.rec (motive := fun _ ↦ ℝ)
  -- simp only at G
  exact G Real.pi (Real.exp 1) (fun _ x ↦ x) (fun n _ _ x y ↦ x * y)

def Cat : NiceType := Tom

def Hunting : NiceType := g 2 Cat Jerry

-- #### Another example

inductive AMSS_Or (p q : Prop) : Prop
| left : p → AMSS_Or p q
| right : q → AMSS_Or p q

#print AMSS_Or

example (n : ℕ) : AMSS_Or (n = 0) (∃ m, n = Nat.succ m) := by
  rcases n with _ | a -- this is a case-splitting on the way a `n : ℕ` can be constructed
  · apply AMSS_Or.left
    rfl
  · apply AMSS_Or.right
    use a

example (n : ℕ) : AMSS_Or (n = 0) (∃ m, n = Nat.succ m) :=
  match n with
  | 0 => by
    apply AMSS_Or.left
    rfl
  | Nat.succ a => by
    apply AMSS_Or.right
    use a

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
  constructor
  · rintro ⟨hP, hQ | hS⟩
    · left
      exact ⟨hP, hQ⟩
    · right
      exact ⟨hP, hS⟩
  · rintro (⟨hP, hQ⟩ | ⟨hP, hS⟩)
    · refine ⟨hP, ?_⟩
      left
      exact hQ
    · exact ⟨hP, Or.inr hS⟩

-- `⌘`

inductive AMSS_Nat
| AMSS_zero : AMSS_Nat
| AMSS_succ : AMSS_Nat → AMSS_Nat
open AMSS_Nat

#print AMSS_Nat
#check AMSS_Nat

def AMSS_Nat_add : AMSS_Nat → AMSS_Nat → AMSS_Nat := fun n m ↦ match n, m with
  | AMSS_zero, m => m
  | AMSS_succ n, m => AMSS_succ (AMSS_Nat_add n m)

-- We want to prove that `AMSS_Nat = ℕ`: after all they are *constructed* in the same way!
#print Equiv

def JustOne_fun : ℕ → AMSS_Nat
  | 0 => AMSS_zero
  | Nat.succ m => AMSS_succ (JustOne_fun m)

def JustOne_inv : AMSS_Nat → ℕ
  | AMSS_zero => 0
  | AMSS_succ a => Nat.succ (JustOne_inv a)

-- The rest of the equivalence is left as an *exercise*.


end InductiveTypes


section Exercises
-- # Exercises

-- **Exercise**
-- What is the type of `¬`?
-- It is `Prop → Prop`:
#check Not

-- **Exercise**
-- Why is `¬ P : Prop` when `P : Prop`?
-- Both `P : Prop` and `False : Prop`, so `P → False : Prop`.


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

-- *1.* `F 2` should be a pair of a proof that `0 ≠ 2` and of the existence of a non-zero
-- 2-dimensional vector for every `v`.
-- *2.* The type of `fun n ↦ (fun (α : Type 2) ↦ Vector α n)` is
-- `ℕ → Type 2 → Type 2`, which belongs to `Type 3`.
-- *3.* The type of `fun (n : ℕ) ↦ (fun (α : Type 2) ↦ ∃ (v w : Vector α n), v ≠ w)` is
-- `ℕ → Type 2 → Prop`
-- *3.* The type of `fun (n : ℕ) ↦ (∀ α : Type 2, ∃ (v w : Vector α n), v ≠ w)` is `ℕ → Prop`, which
-- is of universe level `Type 0` since both `ℕ` and `Prop` are terms in `Type 0`.
-- *4.* The type of `F 2` is a `Prop`, which is of universe level `Type 0`.
-- *5.* No, it is false: among all types in `Type 2` there is the empty type, for which it is
-- impossible to find two different 2-dimensional vectors.
-- *6.* `F` is of type `ℕ ↦ Prop`, of level `Type 0`.


variable (α : Type*) (p q : α → Prop) -- Use `\alpha` to write `α`

-- **Exercise**
example : True → True := by
  intro h
  exact h

-- **Exercise**
example : (P → False) → P → Q := by
  intro h hP
  exfalso
  apply h
  exact hP

-- **Exercise**
example : P → ¬ P → False := by
  intro hP hneP
  apply hneP
  exact hP

-- **Exercise**
example : (P → ¬ Q) → (Q → ¬ P) := by
  intro t_to_f h_neQ
  by_contra h
  have H := t_to_f h
  apply H
  exact h_neQ

-- **Exercise**
example (h : ¬ (2 = 2)) : P → Q := by
  by_contra
  -- exfalso
  apply h
  rfl

-- **Exercise**
example : (∀ x : α, p x ∧ q x) → ∀ x : α, p x := by
  intro h
  intro x
  exact (h x).left

-- **Exercise**
example : (∀ x, p x ∨ R) ↔ (∀ x, p x) ∨ R := by
  constructor
  · intro h
    by_cases hR : R
    · right
      exact hR
    · left
      intro x
      specialize h x
      cases h
      · assumption
      · exfalso
        apply hR
        assumption
  · intro h
    intro x
    by_cases hR : R
    · right
      exact hR
    · left
      exact Or.resolve_right h hR x

-- **Exercise**
example (h : ∃ x, p x ∧ q x) : ∃ x, p x := by
  obtain ⟨y, hy⟩ := h
  use y
  exact hy.1

-- **Exercise**
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := by
  cases h with
  | intro x h =>
    use x
    constructor
    · exact h.right
    · exact h.left

-- **Exercise**
example (a : α) : (∃ x, p x → R) ↔ ((∀ x, p x) → R) := by
  constructor
  · intro h1 h2
    cases h1 with
    | intro x h =>
      exact h (h2 x)
  · contrapose
    intro h
    rw [not_exists] at h
    -- rw [Classical.not_imp]
    rw [_root_.not_imp]
    constructor
    · intro x
      specialize h x
      rw [Classical.not_imp] at h
      exact h.1
    · specialize h a
      rw [Classical.not_imp] at h
      exact h.2

-- **Exercise**
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, hpx | hqx ⟩ := h
    · left
      exact ⟨x, hpx⟩
    · right
      exact ⟨x, hqx⟩
  · rcases h with ⟨x, hx⟩ | ⟨x, hx⟩
    · use x
      left
      exact hx
    · use x
      tauto

-- **Exercise**
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro H
    obtain ⟨x, hx⟩ := H
    apply hx
    exact h x
  · intro x
    rw [not_exists] at h
    specialize h x
    by_contra
    apply h this

-- **Exercise**
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · push_neg
    assumption
  · rw [not_forall] at h
    obtain ⟨x, hx⟩ := h
    use x
    rwa [not_not] at hx

-- **Exercise**
example : (∀ x, p x → R) ↔ (∃ x, p x) → R := by
  refine ⟨fun ha ⟨x, hx⟩ ↦ ?_, fun h x hx ↦ ?_⟩
  · exact ha x hx
  · apply h
    use x


open Function


/- **Exercise**
In the following steps, you're required to complete the proof that `JustOne` is an equivalence
between `AMSS_Nat` and `ℕ`. -/
open AMSS_Nat


def JustOne_Left : LeftInverse JustOne_inv JustOne_fun := by
  intro n
  induction n with --I've pre-populated the structure, but if you type `induction n with`, Lean asks
  -- for the right fields
  | zero => rfl
  | succ m hm => rw [JustOne_fun, JustOne_inv, hm]

def JustOne_Right : RightInverse JustOne_inv JustOne_fun
  | AMSS_zero => rfl
  | AMSS_succ m => by rw [JustOne_inv, JustOne_fun, JustOne_Right]


def JustOne : ℕ ≃ AMSS_Nat where
  toFun := JustOne_fun
  invFun := JustOne_inv
  left_inv := JustOne_Left
  right_inv := JustOne_Right


/- **Exercise**
The successor is not surjective, but you can't rely on the library. -/
example : ¬ Surjective AMSS_succ := by
  intro habs
  obtain ⟨a, ha⟩ := habs AMSS_zero
  cases ha

/- **Exercise**
   Define an inductive type `Politics` with two terms : `Right` and `Left`-/
inductive Politics
  | Right : Politics
  | Left : Politics

-- leave this line as it is
open Politics

/- **Exercise**
Define a function `swap : Politics → Politics` sending `Right` to `Left` and viceversa-/
def swap : Politics → Politics
  | Right => Left
  | Left => Right

/- **Exercise**
State and prove that if someone is not on the `Right`, they are on the `Left` -/
example (a : Politics) : a ≠ Right → a = Left := by
  intro ha
  cases a
  · exfalso
    trivial
  · rfl

-- **Exercise**
-- Can you write down on paper, without using VSCode, the type of `Iff.rec`?

-- associativity of `∨`
-- **Exercise**
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · intro h
    rcases h with h1 | h2
    · rcases h1 with h11 | h12
      · left
        exact h11
      · right
        left
        exact h12
    · right
      right
      exact h2
  · intro h
    rcases h with h1 | h2
    · left
      left
      exact h1
    · rcases h2 with h21 | h22
      · left
        right
        exact h21
      · right
        exact h22


end Exercises
