import Mathlib.Tactic

open Set Classical
open Filter Topology

-- # §1: Sets

open scoped Set
section Definitions


-- **An error**
example (S : Set) := sorry
example {α : Type} (S : Set α) : S = S := by
  rfl

-- `⌘`

-- **A tautology**
example (α : Type) (x : α) (S : Set α) : x ∈ S ↔ S x := by
  rfl


-- *Anonymous function notation*
-- **The positive integers**
def PositiveIntegers : Set ℤ := by
  -- intro d
  --  use if 0 < d then True else False
  -- *or* exact (fun d ↦ 0 < d)
  -- *or* exact (0 < ·) d
  exact (0 < ·)


lemma one_posint : 1 ∈ PositiveIntegers := by
  -- unfold PositiveIntegers
  -- rw [Set.mem_def]
  -- have := Nat.one_pos
  -- exact this -- *why does this fail?*
  -- rw [← Int.ofNat_lt] at this
  -- exact this
  -- *A better proof*
  exact Int.zero_lt_one

-- **The even naturals**

def EvenNaturals : Set ℕ := by
  -- intro d
  -- exact if d % 2 = 0 then True else False
  exact (· % 2 = 0)

example (n : ℕ) : n ∈ EvenNaturals → (n + 2) ∈ EvenNaturals := by
  intro h
  replace h := h.out
  -- rw [Nat.add_mod_right]-- a pity it does not work...
  -- rw [mem_def]
  rw [← Nat.add_mod_right] at h -- try to comment the `replace` three lines above
  exact h


-- **An abstract set**
def AbstractSet {α : Type} (P : α → Prop) : Set α := P
def AbstractSet' {α : Type} (P : α → Prop) : Set α := setOf P

/- The same, but it is a general principle that the second version is better because it
avoids abusing `defeq`. -/
example {α : Type} (P : α → Prop) : AbstractSet P = AbstractSet' P := by
  rfl


-- `⌘`


-- **Subsets as implication**
example {α : Type} (S T : Set α) (s : α) (hST : S ⊆ T) (hs : s ∈ S) : s ∈ T := by
  apply hST
  exact hs

-- **A double inclusion**
example (α : Type) (S T W : Set α) (hST : S ⊆ T) (hTW : T ⊆ W) : S ⊆ W := by
  intro s hs
  apply hTW
  apply hST
  exact hs
  -- *An alternative proof*
  -- intro s hs
  -- exact hTW <| hST hs
  -- *Another one*
  -- exact hTW (hST hs)


-- Why does this *fail*? How to fix it?
-- example : ∀ n : PositiveIntegers, 0 ≤ n := sorry
/- *Sol.:*  This fails because `0` is a term of `ℕ`, whereas `n` is a term of `PositiveIntegers`.
They cannot be compared directly, because `n` is actually a *pair* of a natural number and a proof
of its positivity. It can be made to work as follows-/
example : ∀ n : PositiveIntegers, 0 < n.1 := by
  rintro ⟨-, hn⟩ --use first `rintro ⟨n, hn⟩` and then `rintro ⟨_, hn⟩`
  exact hn

--Sets can be interpreted as types on their own
def rest (α β : Type*) (f : α → β) (S : Set β) (h : ∀ a : α, f a ∈ S) : α → S := by
  intro a
  exact ⟨f a, h a⟩

-- This is enforced through the
variable (α : Type*) in
#synth CoeSort (Set α) (Type _)

-- `⌘`

end Definitions

section Operations

-- ## Operations on sets

-- **Self-intersection is the identity, proven with extensionality**
example (α : Type) (S : Set α) : S ∩ S = S := by
  -- ext
  -- constructor
  -- · intro h --rintro ⟨h, h⟩
  --   exact h.1 -- exact h
  -- · intro h
  --   exact ⟨h, h⟩
-- *Alternative proof*
  ext
  rw [← eq_iff_iff]
  exact and_self _


-- **The union**
example (α : Type) (S T : Set α) (H : S ⊆ T) : S ∪ T = T := by
  ext x
  rw [Set.subset_def] at H
  exact or_iff_right_of_imp (H x)


-- **An _unfixable_ problem**
-- example (α β : Type) (S : Set α) (T : Set β) : S ⊆ S ∪ T := sorry
/- *Sol.:*  Well, it was unfixable, so there is no solution...-/


-- `⌘`


-- **Empty set**
example : (setOf (0 < ·) : Set ℤ) ∩ setOf (· < 0) = ∅ := by
  ext d
  constructor
  · rintro ⟨h_pos, h_neg⟩
    rw [mem_setOf_eq] at h_neg h_pos
    rw [lt_iff_not_ge] at h_neg
    apply h_neg
    apply le_of_lt
    exact h_pos
  · intro h
    exfalso
    exact h


-- `⌘`

-- **§ Indexed unions**
example {α I : Type} (A : I → Set α) (x : α) : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := by
  -- refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ -- it is nice to use `refine` when dealing with an `↔`
  -- · rw [mem_iUnion] at h
  --   exact h
  -- · rw [mem_iUnion]
  --   exact h
  -- -- *Alternative proof*
  simp -- try also `simp?` to see what has been used

-- `⌘`

end Operations


section Filter


variable {α β γ : Type*}

lemma mono (f : α → β) {F G : Filter α} (h : F ≤ G) : F.map f ≤ G.map f := /- fun _ H ↦ h H -/by
  simp only [Filter.le_def, mem_map] --remove after first trial
  intro U hU
  apply h --remove after first trial
  exact /- h -/ hU


/-- The function `f` tends to `G` along `F`. -/
def Tendsto_ENS (f : α → β) (F : Filter α) (G : Filter β) := F.map f ≤ G
#print Tendsto

lemma Tendsto_comp {s : α → β} {t : β → γ} {F : Filter α} {G : Filter β} {H : Filter γ}
    (hs : Tendsto s F G) (ht : Tendsto t G H) : Tendsto (t ∘ s) F H := by --remove
  rw [Tendsto] --remove
  have := mono t hs --remove
  apply le_trans this ht --remove
  -- le_trans (mono t hs) ht


example (f g : ℝ → ℝ) (hf : Tendsto f (𝓝 0) (𝓝 Real.pi))
    (hg : Tendsto g (𝓝 Real.pi) atTop) : Tendsto (g ∘ f) (𝓝 0) atTop := by
  apply Tendsto_comp hf hg

example (a : ℕ → ℝ) (φ : ℝ → ℂ) (ha : Tendsto a atTop (𝓝 (-1)))
    (hφ : Tendsto φ (𝓝 (-1)) (𝓝 (Complex.I))) : Tendsto (φ ∘ a) atTop (𝓝 (Complex.I)) := by
  apply Tendsto_comp ha hφ

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
    {x | p x ∧ q x ∨ p' x ∧ q' x} ∈ 𝓝 x := by
  filter_upwards [hT, hT', hS, hS'] with a ha ha' hb hb' using (by tauto)

-- `⌘`


section EventuallyFrequently

lemma EventuallyLTOne : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < 1 := by
  rw [Filter.eventually_iff]
  rw [mem_nhds_iff]
  use Ioo (-1 : ℝ) (1 : ℝ)
  refine ⟨?_, isOpen_Ioo, by aesop⟩
  · apply subset_of_eq
    grind

example : ∃ᶠ (n : ℕ) in atTop, Even n := by
  rw [frequently_atTop]
  intro n
  use 2 * n
  constructor
  · linarith
  · simp only [even_two, Even.mul_right]

end EventuallyFrequently

-- `⌘`

section Limit


-- Some classical limits
example : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) := by
  exact tendsto_const_div_atTop_nhds_zero_nat 1

-- The pleasure of division in `ℕ`:
example : Tendsto (fun n : ℕ ↦ 1 / n) atTop (𝓝 0) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop 1] with n hn
  rw [Nat.div_eq_of_lt hn]


#check Tendsto.congr'

#check Filter.eventually_ne_atTop

example : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) / n) atTop (𝓝 1) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have h2 : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h3 := Tendsto.add h1 h2
  rw [zero_add] at h3
  refine Tendsto.congr' ?_ h3
  rw [Filter.EventuallyEq]
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [add_div, div_self]
  · ring
  · rwa [Nat.cast_ne_zero]

theorem lemma1 : Tendsto (fun n : ℕ ↦ n ^ 2) atTop atTop := by
  rw [tendsto_pow_atTop_iff]
  exact two_ne_zero

theorem lemma2 : Tendsto (fun n : ℕ ↦ n ^ 2 + n) atTop atTop := by
  apply Tendsto.atTop_add_atTop
  · exact lemma1
  exact tendsto_natCast_atTop_atTop

-- Squeeze theorem(s)
#check tendsto_of_tendsto_of_tendsto_of_le_of_le
#check tendsto_of_tendsto_of_tendsto_of_le_of_le'

example : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ 2 + 4 * Real.sqrt n) / (n ^ 2)) atTop (𝓝 1) := by
  have l1 : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have l2 : Tendsto  (fun n : ℕ ↦ ((n : ℝ) ^ 2 + n) / (n ^ 2)) atTop (𝓝 1) := by
    have l3 : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have l4 := Tendsto.add l1 l3
    rw [add_zero] at l4
    refine Tendsto.congr' ?_ l4
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' l1 l2 ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rw [one_le_div₀, le_add_iff_nonneg_right]
    · positivity
    · positivity
  · filter_upwards [eventually_ge_atTop 16] with n hn
    gcongr
    calc 4 * √↑n ≤ √↑n * √↑n := by
              apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg ↑n)
              apply Real.le_sqrt_of_sq_le
              norm_num
              assumption
                  _  = ↑n := by rw [← Real.sqrt_mul, Real.sqrt_mul_self] <;> norm_cast <;> linarith

example (f : ℝ → ℝ) (g : ℝ → ℝ) (a l : ℝ) (hf : Tendsto f (𝓝 a) (𝓝 l)) (h : f = g) :
    Tendsto g (𝓝 a) (𝓝 l) := by
  exact Tendsto.congr (congrFun h) hf

-- Congruence for limits
example (f : ℝ → ℝ) (g : ℝ → ℝ) (a l : ℝ) (hf : Tendsto f (𝓝 a) (𝓝 l)) (h : f =ᶠ[𝓝 a] g) :
    Tendsto g (𝓝 a) (𝓝 l) := by
  exact (tendsto_congr' h).mp hf

end Limit


end Filter

section Exercises


example : 1 ∉ EvenNaturals := by
  intro h
  trivial
  -- tauto

example : -1 ∉ PositiveIntegers := by
  intro h
  trivial
  -- tauto

-- Define the set of even, positive numbers
def EvenPositiveNaturals : Set PositiveIntegers := by
  rintro ⟨d, _⟩
  exact d % 2 = 0

-- Why does this *fail*? How to fix it?
-- example : 1 ∉ EvenPositiveNaturals := sorry
/- *Sol.:* Lean complains because `3` is not a term of `EvenNaturals`, so it does not make sense
to check whether it satisfies a property defined on them. It can be made to work by writing -/
example : ⟨1, Int.zero_lt_one⟩ ∉ EvenPositiveNaturals := by
  intro h
  cases h

-- Define the set of odd numbers and prove some properties
def OddNaturals : Set ℕ := (· % 2 = 1)

-- Your definition will be right if the following compiles:
example : 3 ∈ OddNaturals := by
  rfl


example (n : ℕ) : n ∈ OddNaturals ↔ n ∉ EvenNaturals := by
  constructor
  · intro h h_abs
    replace h : n % 2 = 1 := h
    replace h_abs : n % 2 = 0 := h_abs
    rw [h] at h_abs
    apply Nat.one_ne_zero
    exact h_abs
  · intro h
    replace h : ¬ n % 2 = 0 := h
    rwa [← ne_eq, Nat.mod_two_ne_zero] at h


-- Consider the following two definigions
def subsub {α : Type} {S : Set α} (P : S → Prop) : Set (S : Type) := P
def subsub' {α : Type} {S : Set α} (P : α → Prop) : Set (S : Type) := by
  intro a
  exact P a

-- Why does this *fail*?
example (α : Type) (S : Set α) : subsub = subsub' := sorry
/- *Sol.:*  Lean complains because in `subsub'` `P` is defined on the type `α` whereas in `subsub`
it is defined on the type `↑S`. So this is an equality between functions defined on different types,
that makes no sense. -/

-- Try to prove the statement proven before, but without using the library
example (α : Type) (S T : Set α) (H : S ⊆ T) : T = S ∪ T := by
  ext
  constructor
  · intro h
    apply Or.intro_right
    exact h
  · intro h
    cases h
    · apply H
      assumption
    · assumption

example (α : Type) (S T R : Set α) : S ∩ (T ∪ R) = (S ∩ T) ∪ (S ∩ R) := by
  ext x
  refine ⟨fun ⟨h1, h2⟩ ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · rcases h2 with hT | hR
    · exact Or.intro_left _ (⟨h1, hT⟩ : And _ _ )
    · exact Or.intro_right _ (⟨h1, hR⟩ : And _ _ )
  · rcases h with ⟨hS, -⟩ | ⟨hS, -⟩ <;> assumption
  · rcases h with ⟨-, hT⟩ | ⟨-, hR⟩
    · left ; exact hT
    · right ; exact hR


example (α : Type) (S : Set α) : Sᶜ ∪ S = univ := by
  ext x
  constructor
  · intro
    trivial
  · intro
    by_cases hx : x ∈ S
    · apply Or.intro_right
      exact hx
    · exact Or.intro_left _ hx

-- For this, you can try `simp` at a certain point...`le_antisymm` can also be useful.
example : (setOf (0 ≤ ·) : Set ℤ) ∩ setOf (· ≤ 0) = {0} := by
  ext
  simp only [mem_inter_iff, mem_setOf_eq, mem_singleton_iff]
  constructor
  · intro h
    exact (le_antisymm h.1 h.2).symm
  · intro h
    rw [h]
    exact ⟨le_refl _, le_refl _⟩


-- Using your definition of `OddNaturals` prove the following:
example : EvenNaturals ∪ OddNaturals = univ := by
  ext x
  simp only [mem_union, mem_univ, iff_true] -- to be obtained by typing `simp?`
  by_cases hx : x % 2 = 0
  · apply Or.inl
    exact hx
  · rw [← ne_eq, Nat.mod_two_ne_zero] at hx
    apply Or.inr
    exact hx


-- **§** A bit of difference, inclusion and intersection
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := by
  ext
  exact ⟨fun ⟨hT, hnS⟩ ↦ hnS <| h hT, fun _ ↦ by trivial⟩


example (α : Type) (S T R : Set α) : S \ (T ∪ R) ⊆ (S \ T) \ R := by
  intro x ⟨hxS, hxnTR⟩
  rw [mem_diff]
  rw [mem_union, not_or] at hxnTR
  exact ⟨⟨hxS, fun h ↦ hxnTR.1 h⟩, hxnTR.2⟩
-- *An alternative tactic* replacing this `exact`: longer but easier to read:
  -- constructor
  -- · constructor
  --   · exact hxS
  --   · exact hxnTR.1
  -- exact hxnTR.2


-- Indexed intersections work as indexed unions (_mutatis mutandis_)
example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example {α I : Type} (A : I → Set α) (S : Set α) : (S ∩ ⋃ i, A i) = ⋃ i, A i ∩ S := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

open Real

lemma frequently_one : ∃ᶠ (x : ℝ) in atTop, sin x = 1 := by
  rw [frequently_atTop]
  intro a
  use 2 * (⌈a⌉₊ + 1)* Real.pi + Real.pi/2
  constructor
  · have := Real.pi_nonneg
    have := Real.one_le_pi_div_two
    calc 2 * (⌈a⌉₊ + 1)* Real.pi + Real.pi/2 ≥ 2 * (⌈a⌉₊ + 1) * Real.pi := by grind
                                        _ ≥ 2 * (⌈a⌉₊ + 1) := by
                                              norm_num
                                              apply le_mul_of_one_le_right
                                              · linarith
                                              · linarith [Real.one_le_pi_div_two]
    linarith [Nat.le_ceil (a := a)]
  · rw [sin_add]
    norm_cast
    rw [Real.sin_nat_mul_pi, zero_mul, zero_add, Real.cos_nat_mul_pi, sin_pi_div_two, mul_one]
    norm_num

lemma frequently_neg_one : ∃ᶠ (x : ℝ) in atTop, sin x = -1 := by
  rw [frequently_atTop]
  intro a
  use (2 * ⌈a⌉₊ + 1)* Real.pi + Real.pi/2
  constructor
  · have := Real.pi_nonneg
    have := Real.one_le_pi_div_two
    calc (2 * ⌈a⌉₊ + 1) * Real.pi + Real.pi/2 ≥ (2 * ⌈a⌉₊ + 1) * Real.pi := by grind
                                        _ ≥ 2 * ⌈a⌉₊ + 1 := by
                                              norm_num
                                              apply le_mul_of_one_le_right
                                              · linarith
                                              · linarith [Real.one_le_pi_div_two]
    linarith [Nat.le_ceil (a := a)]
  · rw [sin_add]
    norm_cast
    rw [Real.sin_nat_mul_pi, zero_mul, zero_add, Real.cos_nat_mul_pi, sin_pi_div_two, mul_one]
    norm_num
    

example (t : ℝ) : ¬ Tendsto (fun x ↦ Real.sin x) atTop (𝓝 t) := by
  by_cases ht : t = 1
  · have hU : ∃ U ∈ (𝓝 t), -1 ∉ U := by
      refine ⟨Icc (-1/2) (3/2), ?_, by simp⟩
      · simp [ht]; constructor <;> linarith
    obtain ⟨U, hU, hU_mem⟩ := hU
    rw [tendsto_def]
    simp only [mem_atTop_sets, ge_iff_le, mem_preimage, not_forall, not_exists]
    by_contra! H
    specialize H U hU
    obtain ⟨a, ha⟩ := H
    have hf := frequently_neg_one
    simp only [frequently_iff, mem_atTop_sets, ge_iff_le, forall_exists_index] at hf
    obtain ⟨b, hb_mem, hb_ge⟩ := @hf {x : ℝ | a ≤ x} a (by simp)
    specialize ha b hb_mem
    rw [hb_ge] at ha
    tauto
  · have hU : ∃ U ∈ (𝓝 t), 1 ∉ U := by
      simp only [← disjoint_nhds_nhds, Filter.disjoint_iff] at ht
      obtain ⟨U, hU, X, hX_one, hUX⟩ := ht
      refine ⟨U, hU, ?_⟩
      apply Disjoint.notMem_of_mem_right hUX
      exact mem_of_mem_nhds hX_one      
    obtain ⟨U, hU, hU_mem⟩ := hU
    rw [tendsto_def]
    simp only [mem_atTop_sets, ge_iff_le, mem_preimage, not_forall, not_exists]
    by_contra! H
    specialize H U hU
    obtain ⟨a, ha⟩ := H
    have hf := frequently_one
    simp only [frequently_iff, mem_atTop_sets, ge_iff_le, forall_exists_index] at hf
    obtain ⟨b, hb_mem, hb_ge⟩ := @hf {x : ℝ | a ≤ x} a (by simp)
    specialize ha b hb_mem
    rw [hb_ge] at ha
    tauto

/- If the sequence `u` converges to `x` and `u n` is in `M` for `n` big enough,
then `x` is in the closure of `M`: a couple of useful lemmas, before:. -/
#check mem_closure_iff_clusterPt
#print ClusterPt
#check le_principal_iff
#check neBot_of_le
-- Here you go!
example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M := by
  rw [mem_closure_iff_clusterPt]
  change (𝓝 x ⊓ 𝓟 M).NeBot
  apply neBot_of_le (f := map u atTop)
  rw [le_inf_iff]
  refine ⟨hux, ?_⟩
  refine le_trans (map_mono (m := u) (le_principal_iff.mpr huM)) ?_
  simp only [map_principal, le_principal_iff, mem_principal, image_subset_iff]
  intro x
  simp


example : ∀ᶠ x in nhds (0 : ℝ), |x| ≤ 1/2 := by
  dsimp [Filter.Eventually]
  rw [(nhds_basis_Ioo_pos 0).mem_iff]
  use 1/2
  constructor
  · simp only [one_div, inv_pos, Nat.ofNat_pos]
  · simp only [zero_sub, zero_add]
    intro x ⟨hx₁, hx₂⟩
    rw [mem_setOf_eq, abs_le]
    exact ⟨le_of_lt hx₁, le_of_lt hx₂⟩


-- There are rationals of the form `1/n` that are arbitrarily close to `0`.
example : ∃ᶠ x in 𝓝 (0 : ℝ), ∃ n : ℤ, x = 1 / (n : ℝ) := by
  rw [frequently_nhds_iff]
  intro U hU_mem hU_open
  rw [Metric.isOpen_iff] at hU_open
  obtain ⟨ε, ε_pos, hε⟩ := hU_open 0 hU_mem
  set L := Nat.ceil ε⁻¹ + 1 with hL₀
  have hL : (L : ℝ)⁻¹ < ε := by
    rw [hL₀]
    rw [inv_lt_iff_one_lt_mul₀, Nat.cast_add, mul_add, Nat.cast_one, mul_one, ← sub_lt_iff_lt_add]
    · calc 1 - ε < 1 := by simp_all
      _ = ε * ε⁻¹ := by rw [mul_inv_cancel₀ (ne_of_gt ε_pos)]
      _ ≤ ε * (⌈ ε⁻¹ ⌉₊ : ℝ) := by
        rw [mul_le_mul_iff_of_pos_left (ε_pos)]
        exact Nat.le_ceil ε⁻¹
    · norm_cast
      omega
  use (L : ℝ)⁻¹
  constructor
  · apply hε
    simpa
  · use L
    simp


end Exercises
