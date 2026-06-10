import Mathlib.Tactic

open Set Classical
open Filter Topology

-- # §1: Sets

open scoped Set
section Definitions


-- **An error**
example (S : Set) := sorry
example {α : Type} (S : Set α) : S = S := sorry

-- `⌘`

-- **A tautology**
example (α : Type) (x : α) (S : Set α) : x ∈ S ↔ S x := sorry


-- **The positive integers**
def PositiveIntegers : Set ℤ := sorry


lemma one_posint : 1 ∈ PositiveIntegers := sorry

-- **The even naturals**
def EvenNaturals : Set ℕ := sorry

example (n : ℕ) : n ∈ EvenNaturals → (n + 2) ∈ EvenNaturals := sorry


-- **An abstract set**
def AbstractSet {α : Type} (P : α → Prop) : Set α := P
def AbstractSet' {α : Type} (P : α → Prop) : Set α := setOf P

/- The same, but it is a general principle that the second version is better because it
avoids abusing `defeq`. -/
example {α : Type} (P : α → Prop) : AbstractSet P = AbstractSet' P := sorry


-- `⌘`


-- **Subsets as implication**
example {α : Type} (S T : Set α) (s : α) (hST : S ⊆ T) (hs : s ∈ S) : s ∈ T := sorry


-- **A double inclusion**
example (α : Type) (S T W : Set α) (hST : S ⊆ T) (hTW : T ⊆ W) : S ⊆ W := sorry


-- Why does this *fail*? How to fix it?
-- example : ∀ n : PositiveIntegers, 0 ≤ n := sorry
/- *Sol.:*  This fails because `0` is a term of `ℕ`, whereas `n` is a term of `PositiveIntegers`.
They cannot be compared directly, because `n` is actually a *pair* of a natural number and a proof
of its positivity. It can be made to work as follows-/
example : ∀ n : PositiveIntegers, 0 < n.1 := sorry

--Sets can be interpreted as types on their own
def rest (α β : Type*) (f : α → β) (S : Set β) (h : ∀ a : α, f a ∈ S) : α → S := sorry

-- This is enforced through the
variable (α : Type*) in
#synth CoeSort (Set α) (Type _)

-- `⌘`

end Definitions

section Operations

-- ## Operations on sets

-- **Self-intersection is the identity, proven with extAMSSionality**
example (α : Type) (S : Set α) : S ∩ S = S := sorry


-- **The union**
example (α : Type) (S T : Set α) (H : S ⊆ T) : S ∪ T = T := sorry


-- **An _unfixable_ problem**
example (α β : Type) (S : Set α) (T : Set β) : S ⊆ S ∪ T := sorry


-- `⌘`


-- **Empty set**
example : (setOf (0 < ·) : Set ℤ) ∩ setOf (· < 0) = ∅ := sorry


-- `⌘`

-- **§ Indexed unions**
example {α I : Type} (A : I → Set α) (x : α) : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := sorry

-- `⌘`

end Operations


section Filter


variable {α β γ : Type*}

lemma mono (f : α → β) {F G : Filter α} (h : F ≤ G) : F.map f ≤ G.map f := sorry


/-- The function `f` tends to `G` along `F`. -/
def Tendsto_AMSS (f : α → β) (F : Filter α) (G : Filter β) := F.map f ≤ G
#print Tendsto

lemma Tendsto_comp {s : α → β} {t : β → γ} {F : Filter α} {G : Filter β} {H : Filter γ}
    (hs : Tendsto s F G) (ht : Tendsto t G H) : Tendsto (t ∘ s) F H := sorry


example (f g : ℝ → ℝ) (hf : Tendsto f (𝓝 0) (𝓝 Real.pi))
    (hg : Tendsto g (𝓝 Real.pi) atTop) : Tendsto (g ∘ f) (𝓝 0) atTop := sorry


example (a : ℕ → ℝ) (φ : ℝ → ℂ) (ha : Tendsto a atTop (𝓝 (-1)))
    (hφ : Tendsto φ (𝓝 (-1)) (𝓝 (Complex.I))) : Tendsto (φ ∘ a) atTop (𝓝 (Complex.I)) := sorry

/-
`filter_upwards [h₁, ⋯, hₙ]` replaces a goal of the form `s ∈ f` and terms
`h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` with `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`.
The list is an optional parameter, `[]` being its default value.

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` is a short form for
`{ filter_upwards [h₁, ⋯, hₙ], intro a₁ a₂ ⋯ aₖ }`.

`filter_upwards [h₁, ⋯, hₙ] using e` is a short form for
`{ filter_upwards [h1, ⋯, hn], exact e }`.

Combining both shortcuts is done by writing `filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`.
Note that in this case, the `aᵢ` terms can be used in `e`.
-/

example [TopologicalSpace α] {x : α} {p p' q q' : α → Prop}
    (hT : {x | p x} ∈ 𝓝 x)
    (hT' : {x | p' x} ∈ 𝓝 x)
    (hS : {x | q x} ∈ 𝓝 x)
    (hS' : {x | q' x} ∈ 𝓝 x) :
    {x | p x ∧ q x ∨ p' x ∧ q' x} ∈ 𝓝 x := sorry

-- `⌘`


section EventuallyFrequently

lemma EventuallyLTOne : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < 1 := sorry


example : ∃ᶠ (n : ℕ) in atTop, Even n := sorry

end EventuallyFrequently

-- `⌘`

section Limit


-- Some classical limits
example : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) := sorry


-- The pleasure of division in `ℕ`:
example : Tendsto (fun n : ℕ ↦ 1 / n) atTop (𝓝 0) := sorry


#check Tendsto.congr'

#check Filter.eventually_ne_atTop

example : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) / n) atTop (𝓝 1) := sorry


theorem lemma1 : Tendsto (fun n : ℕ ↦ n ^ 2) atTop atTop := sorry

theorem lemma2 : Tendsto (fun n : ℕ ↦ n ^ 2 + n) atTop atTop := sorry

-- Squeeze theorem(s)
#check tendsto_of_tendsto_of_tendsto_of_le_of_le
#check tendsto_of_tendsto_of_tendsto_of_le_of_le'

example : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ 2 + 4 * Real.sqrt n) / (n ^ 2)) atTop (𝓝 1) := sorry

example (f : ℝ → ℝ) (g : ℝ → ℝ) (a l : ℝ) (hf : Tendsto f (𝓝 a) (𝓝 l)) (h : f = g) :
    Tendsto g (𝓝 a) (𝓝 l) := sorry

-- Congruence for limits
example (f : ℝ → ℝ) (g : ℝ → ℝ) (a l : ℝ) (hf : Tendsto f (𝓝 a) (𝓝 l)) (h : f =ᶠ[𝓝 a] g) :
    Tendsto g (𝓝 a) (𝓝 l) := sorry

end Limit


end Filter

section Exercises


example : 1 ∉ EvenNaturals := sorry


example : -1 ∉ PositiveIntegers := sorry

-- Define the set of even, positive numbers
def EvenPositiveNaturals : Set PositiveIntegers := sorry


-- Why does this *fail*? How to fix it?
example : 1 ∉ EvenPositiveNaturals := sorry

-- Define the set of odd numbers and prove some properties
def OddNaturals : Set ℕ := sorry

-- Your definition will be right if the following compiles:
example : 3 ∈ OddNaturals := sorry


example (n : ℕ) : n ∈ OddNaturals ↔ n ∉ EvenNaturals := sorry

-- Consider the following two definigions
def subsub {α : Type} {S : Set α} (P : S → Prop) : Set (S : Type) := P
def subsub' {α : Type} {S : Set α} (P : α → Prop) : Set (S : Type) := by
  intro a
  exact P a

-- Why does this *fail*?
example (α : Type) (S : Set α) : subsub = subsub' := sorry


-- Try to prove the statement proven before, but without using the library
example (α : Type) (S T : Set α) (H : S ⊆ T) : T = S ∪ T := sorry

example (α : Type) (S T R : Set α) : S ∩ (T ∪ R) = (S ∩ T) ∪ (S ∩ R) := sorry


example (α : Type) (S : Set α) : Sᶜ ∪ S = univ := sorry

-- For this, you can try `simp` at a certain point...`le_antisymm` can also be useful.
example : (setOf (0 ≤ ·) : Set ℤ) ∩ setOf (· ≤ 0) = {0} := sorry


-- Using your definition of `OddNaturals` prove the following:
example : EvenNaturals ∪ OddNaturals = univ := sorry


-- **§** A bit of difference, inclusion and intersection
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := sorry


example (α : Type) (S T R : Set α) : S \ (T ∪ R) ⊆ (S \ T) \ R := sorry


-- Indexed intersections work as indexed unions (_mutatis mutandis_)
example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := sorry


example {α I : Type} (A : I → Set α) (S : Set α) : (S ∩ ⋃ i, A i) = ⋃ i, A i ∩ S := sorry
open Real

lemma frequently_one : ∃ᶠ (x : ℝ) in atTop, sin x = 1 := sorry

lemma frequently_neg_one : ∃ᶠ (x : ℝ) in atTop, sin x = -1 := sorry


example (t : ℝ) : ¬ Tendsto (fun x ↦ Real.sin x) atTop (𝓝 t) := sorry

/- If the sequence `u` converges to `x` and `u n` is in `M` for `n` big enough,
then `x` is in the closure of `M`: a couple of useful lemmas, before:. -/
#check mem_closure_iff_clusterPt
#print ClusterPt
#check le_principal_iff
#check neBot_of_le
-- Here you go!
example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M := sorry


example : ∀ᶠ x in nhds (0 : ℝ), |x| ≤ 1/2 := sorry

/- There are rationals of the form `1/n` that are arbitrarily close to `0`.
**ToDo** -/
example : ∃ᶠ x in 𝓝 (0 : ℝ), ∃ n : ℤ, x = 1 / (n : ℝ) := sorry


end Exercises
