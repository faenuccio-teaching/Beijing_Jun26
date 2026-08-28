import Mathlib

inductive AMSS_Nat
| AMSS_zero : AMSS_Nat
| AMSS_succ : AMSS_Nat → AMSS_Nat
open AMSS_Nat

-- A structure containing simply a `0` and `+`:
#print AddZero

def AMSS_Nat_add : AMSS_Nat → AMSS_Nat → AMSS_Nat := fun n m ↦ match n, m with
  | AMSS_zero, m => m
  | AMSS_succ n, m => AMSS_succ (AMSS_Nat_add n m)

example : AddZero AMSS_Nat where
  add := AMSS_Nat_add
  zero := AMSS_zero

example : AddMonoid AMSS_Nat where
  add := AMSS_Nat_add
  zero := AMSS_zero
  zero_add (a) := rfl
  add_zero (a) := by
    induction a with
    | AMSS_zero => rfl
    | AMSS_succ b h =>
      change AMSS_succ (AMSS_Nat_add b AMSS_zero) = AMSS_succ b
      apply congrArg AMSS_succ
      exact h
  add_assoc := sorry
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry

-- `⌘`

-- ## Painful examples

example {G : Type*} [Group G] (g e : G) (h : g * e = g) : e = 1 := by
  calc e = 1 * e := by rw [one_mul]
      _ = g⁻¹ * g * e := by rw [← inv_mul_cancel]
      _ = g⁻¹ * (g * e) := by rw [mul_assoc]
      _ = g⁻¹ * g := by rw [h]
      _ = 1 := by rw [inv_mul_cancel]
  -- rw [← left_eq_mul, h]

example {G : Type*} [CommGroup G] (N : Subgroup G) : CommGroup (G ⧸ N) := by
  constructor
  intro a b
  obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective N a
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective N b
  rw [← ha', ← hb'/- , QuotientGroup.mk'_apply, QuotientGroup.mk'_apply-/]
  simp only [QuotientGroup.mk'_apply]
  apply CommGroup.mul_comm
  -- exact QuotientGroup.Quotient.commGroup N

/- Can you understand the error message (I'm not asking whether you understand *why* you get
and error: just what it says). -/
lemma quotComm_lemma {G : Type*} [Group G] (N : Subgroup G) : CommGroup (G ⧸ N) := by sorry

-- This is false, but at least it compiles
def quotComm_def {G : Type*} [Group G] (N : Subgroup G) : Group (G ⧸ N) := by sorry


lemma unit_surj (A B : Type*) [CommRing A] [CommRing B] {f : A →+* B} (a : Aˣ) : IsUnit (f a) := by
  rcases a with ⟨u, v, huv, hvu⟩
  rw [isUnit_iff_exists] -- very strange lemma
  refine ⟨f v, ?_, ?_⟩
  · simp [← map_mul, huv]
  · simp [← map_mul, hvu]

-- `⌘`

noncomputable section Groups

-- ### A wrong way to define mathematical structures

structure WrongGroup where
  carrier : Type*
  one : carrier
  mul : carrier → carrier → carrier
  inv : carrier → carrier
  mul_one : ∀ (x : carrier), mul x one = x
  one_mul : ∀ (x : carrier), mul one x = x
  mul_assoc : ∀ (x y z : carrier), mul (mul x y) z = mul x (mul y z)
  inv_mul_cancel : ∀ (x : carrier), mul (inv x) x = one

lemma WrongGroup.inv_eq_of_mul {α : WrongGroup} (x y : α.carrier) :
    α.mul x y = α.one → α.inv x = y := by
  intro h
  apply_fun (fun z ↦ α.mul (α.inv x) z) at h
      -- use the `apply_fun` tactic to apply a function to both sides of a hypothesis
  rw [α.mul_one, ← α.mul_assoc, α.inv_mul_cancel, α.one_mul] at h
  exact h.symm

structure WrongSemigroup where
  carrier : Type*
  mul : carrier → carrier → carrier
  mul_assoc : ∀ (x y z : carrier), mul (mul x y) z = mul x (mul y z)


lemma assoc_mul (X : WrongSemigroup) (x y z w : X.carrier) :
    X.mul x (X.mul (X.mul y z) w) = X.mul (X.mul x y) (X.mul z w) := by
  rw [X.mul_assoc]
  rw [X.mul_assoc]

lemma assoc_mul' (G : WrongGroup) (x y z w : G.carrier) :
    G.mul x (G.mul (G.mul y z) w) = G.mul (G.mul x y) (G.mul z w) := by
  -- apply assoc_mul -- it does not work!
  simp[G.mul_assoc]

def Nplus : WrongSemigroup where
  carrier := ℕ
  mul := (· + ·) -- or fun x y ↦ x + y
  mul_assoc := add_assoc

example : Nplus.mul 1 1 = 2 := rfl
example : Nplus.mul (1 : Nplus) (1 : Nplus) = (2 : Nplus) := rfl
example : Nplus.mul (1 : ℕ) (1 : ℕ) = (2 : ℕ) := rfl

-- `⌘`

-- ### A good way to define mathematical structures

#print Group
-- and right-clicking on it yields (the `_at_AMSS` avoids Lean complaining this already exists)
structure Group_at_AMSS (G : Type*) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

#print DivInvMonoid

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

#print CommGroup
-- and right-clicking on it yields
structure CommGroup_at_AMSS (G : Type*) extends Group G, CommMonoid G

example {G : Type*} [CommGroup G] (x y : G) : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  -- group
  rw [mul_inv_rev, mul_comm]
  -- rw [mul_inv]

example {A : Type*} [AddCommGroup A] (x y : A) : x + y + 0 = x + y := by
  abel

-- whatsnew in
-- @[to_additive] -- to be uncommented later, in the `Classes` section
lemma mul_square {G : Type*} [Group G] {x y : G} (h : x * y = 1) : x * y ^ 2 = y := by
  rw [pow_two]
  rw [← mul_assoc]
  rw [h]
  group

-- actually `mul_assoc` does not only work for groups.
#check mul_assoc

-- `⌘`

-- ## Classes

example {A : Type*} [AddGroup A] (x y : A) : x + y + 0 = x + y := by
  -- group
  simp only [add_zero] -- when does `add_zero` hold?

#print HAdd
-- @[inherit_doc] infixl:65 " + "   => HAdd.hAdd

#synth Group ℤ
#synth AddGroup ℤ
#synth AddGroup (ℤ × ℤ)

#print One
#synth One ℤ

example : AddGroup (ℤ × ℚ) := inferInstance

example {A : Type*} [AddGroup A] {a b : A} (h : a + b = 0) : a + 2 • b = b := by
  -- exact add_even h -- uncomment @[to_additive]
  rw [two_nsmul, ← add_assoc, h]
  simp

-- What's going on here?
example (G : Type*) [Group G] [CommGroup G] (g : G) : 1 * g = g := by
  rw [one_mul]

-- #### The `Coe` class
#check Complex.exp_add_pi_mul_I (3/2 : ℚ)
#print RatCast
#synth RatCast ℂ

-- Anonymous function def!
instance : Coe WrongGroup Type where
  coe := (·.carrier)

-- instance : CoeSort WrongGroup Type where
--  coe := (·.carrier)


example {α : WrongGroup} (x : α) :
    α.mul x (α.inv x) = α.one := by
  rw [← α.inv_mul_cancel (α.inv x), α.inv_eq_of_mul _ _ (α.inv_mul_cancel x)]

instance : Add Bool where
  add b₁ b₂ := b₁ && b₂

example : true + false = false := by rfl

-- `⌘`

-- ### More about groups

variable (G : Type*) [Group G]

-- #### Subgroups
example (H : Subgroup G) : Group H := inferInstance

variable (H : Subgroup G) in
#synth Group H

/- We have an automatic coercion from sets to types (more about this in the next class),
so we get a coercion from subgroups to types: -/
example (H : Subgroup G) (x : H) (hx : x = 1) : (x : G) = 1 := by
  simp [hx]

example (H : Subgroup G) : 1 ∈ H := H.one_mem

/- Observe what happens if one writes

  `AddSubgroup ℤ :=`
  `_`

-/
example : AddSubgroup ℤ where
  carrier := {n : ℤ | Even n}
  add_mem' := by
    intro a b ha hb
    -- simp at ha hb --not needed, actually
    simp only [Even] at ha hb
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    rw [hn, hm]
    use n + m
    abel
    -- grind
  zero_mem' := ⟨0, by abel⟩
  neg_mem' {x} hx := by
    obtain ⟨r, _⟩ := hx
    exact ⟨-r, by simp_all⟩

/- In the example below, note two things:
1. What happens if we remove `Comm`;
2. What happens to the `G` and `Group G` that are globally defined in this section;
-/
example (G : Type*) [CommGroup G] (H₁ H₂ : Subgroup G) {x y : G} (hx : x ∈ H₁) (hy : y ∈ H₂) :
    x * y ∈ H₁ ⊔ H₂ := by
  rw [Subgroup.mem_sup]
  use x, hx, y, hy

example (x : G) (hx : x ∈ (⊥ : Subgroup G)) : x = 1 := Subgroup.mem_bot.mp hx


---Let's discuss **dot notation**.
example : (Subgroup.center G).Normal := by
-- #print Subgroup.Normal
  apply Subgroup.Normal.mk
  intro z hz g
  let hz' := hz
  rw [Subgroup.mem_center_iff] at hz --this looses hz
  specialize hz g
  rw [← mul_inv_eq_iff_eq_mul] at hz
  rwa [hz]
  -- exact Subgroup.instNormalCenter

-- `⌘`

-- #### Homomorphisms

-- @[ext]
structure MonoidHom_AMSS (M N : Type*) [Monoid M] [Monoid N] where
  toFun : M → N
  map_one : toFun 1 = 1
  map_mul : ∀ (x y : M), toFun (x * y) = (toFun x) * (toFun y)


-- Note the @[ext] tag.
example (G H : Type*) [Group G] [Group H] (f g : MonoidHom_AMSS G H)
    (H : ∀ x, f.toFun x = g.1 x) : f = g := by -- the `f.toFun` and `g.1` are horrible!
  cases f
  cases g
  simp only [MonoidHom_AMSS.mk.injEq]
-- #print MonoidHom_AMSS.mk.injEq
  ext -- x
  apply H

#check MonoidHom.ext

def f : MonoidHom_AMSS (ℕ × ℕ) ℕ where
  toFun p := p.1 * p.2
  map_one := by simp only [Prod.fst_one, Prod.snd_one, mul_one]
  map_mul _ _ := by simp only [Prod.fst_mul, Prod.snd_mul]; group

#check f ⟨2,3⟩ -- we can't apply a `MonoidHom₁` to an element, which is annoying


#check f.toFun ⟨2,3⟩
#eval f.toFun ⟨2,3⟩

/- We would like to able to write `f ⟨2,3⟩` instead of `f.toFun ⟨2,3⟩`. We do this
using the `CoeFun` class, which is a class for objects that can be coerced into
functions.-/

#print CoeFun


instance {G H : Type*} [Monoid G] [Monoid H] :
    CoeFun (MonoidHom_AMSS G H) (fun _ ↦ G → H) where
  coe := MonoidHom_AMSS.toFun

-- attribute [coe] MonoidHom_AMSS.toFun
#check f ⟨2,3⟩

-- whatsnew in
-- @[to_additive __]
example (G₁ : Type) [CommGroup G₁] (f : G →* G₁) : ∀ x y : G, x * y = 1 → (f x) * (f y) = 1 := by
  intro x y h
  rw [← map_mul, h, map_one]

example (A : Type*) [AddGroup A] (f : G →* A) : ∀ x y : G, x * y = 1 → (f x) * (f y) = 1 := by sorry

open Function in
example (A : Type*) [AddGroup A] (f : A →+ ℤ) (hf : 1 ∈ f.range) : Surjective f := by
  rcases hf with ⟨b, hb⟩
  intro m
  use m • b
  simp [map_zsmul, hb]

-- `⌘`

-- #### Quotients

#print Setoid
#print Equivalence
#print Quotient

variable (H : Subgroup G)

#print QuotientGroup.leftRel
#check QuotientGroup.leftRel H
#check (QuotientGroup.mk' _ : [_? : H.Normal] → G →* G ⧸ H)

-- `simpa` & `refine` for `↔`
example (N : Subgroup G) [N.Normal] (x y : G) : (x : G ⧸ N) = (y : G ⧸ N) ↔ x * y⁻¹ ∈ N := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [QuotientGroup.eq] at h
    rw [← inv_inv x, ← mul_inv_rev]
    apply Subgroup.inv_mem
    rwa [Subgroup.Normal.mem_comm_iff]
    assumption
  · rw [QuotientGroup.eq, ← inv_inv y, ← mul_inv_rev]
    apply Subgroup.inv_mem
    simpa [Subgroup.Normal.mem_comm_iff]


/- Class type inference makes Lean understand that since `H` is
commutative, `N` is normal and thus `H ⧸ N` is a group. -/
example (H : Type*) [CommGroup H] (f : H →* G) (N : Subgroup H) (hN : N ≤ f.ker) :
    {g : H ⧸ N →* G // ∀ h : H, f h = g h } := by
  set g := QuotientGroup.lift N f hN with hg -- `set ... with`!
  use g
  intro h
  rw [hg]
  simp only [QuotientGroup.lift_mk]

example [H.Normal] (K : Subgroup G) : Subgroup (G ⧸ H) where
  carrier := QuotientGroup.mk '' K
  one_mem' := by
    simp only [Set.mem_image, SetLike.mem_coe, QuotientGroup.eq_one_iff]
    use 1
    constructor-- <;>
    · exact K.one_mem
    · exact H.one_mem
    -- apply one_mem
  mul_mem' := by
    rintro a b ⟨x, hxa, rfl⟩ ⟨y, hyb, rfl⟩
    exact ⟨x * y, K.mul_mem hxa hyb, rfl⟩
  inv_mem' /- {g} -/ := by
    rintro g ⟨x, ⟨hx, rfl⟩⟩
    -- simp only [Set.mem_image, SetLike.mem_coe]
    use x⁻¹
    exact ⟨K.inv_mem hx, rfl⟩

example [H.Normal] (K : Subgroup G) : Subgroup (G ⧸ H) := K.map (QuotientGroup.mk' H)
example [H.Normal] (K : Subgroup G) : Subgroup (G ⧸ H) := K.map (QuotientGroup.mk H)

-- `⌘`

end Groups

section Rings

#synth Ring ℤ
#synth CommRing ℤ
#synth Monoid ℤ
#synth AddMonoid ℤ
#check CommRing.toCommMonoid
#check CommRing.toAddCommGroupWithOne

example (a b c : ℚ) : a + (b + c * 1) = a + b + c := by
  -- rw [mul_one]
  -- rw [← add_assoc]
  ring

#check mul_one
#check add_assoc
#print AddMonoid
#print Field
#print IsDomain
#print CommMonoid


example (R : Type*) [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring
  -- exact? ==> exact add_pow_two x y

lemma sixth_pow (R : Type*) [CommRing R] (x y : R) : (x + y) ^ 6 =
    x ^ 6 + 6 * x ^ 5 * y +  15 * x ^ 4 * y ^ 2 + 20 * x ^ 3 * y ^ 3 +
      15 * x ^ 2 * y ^ 4 + 6 * x * y ^ 5 + y ^ 6 := by
  ring
  -- grind
  -- exact?

#print axioms sixth_pow

example (R : Type*) [CommRing R] (x y : R) (H : x ^ 2 ≠ y ^ 2) : x ≠ y := by
  -- ring
  grind

variable {R S : Type*} [CommRing R] [CommRing S]

example (f : R →+* S) (r : R) : IsUnit r → IsUnit (f r) := by
  unfold IsUnit
  -- use r -- the arrow `↑u` is there for a reason...
  intro h
  -- obtain ⟨v, hv⟩ := h -- probably not enough: what does it mean `v : Rˣ`? Let's hover on it...
  obtain ⟨⟨v, u, hvu, huv⟩, H⟩ := h
  -- simp only at H
  fconstructor
  · use f r
    · use (f u)
    · rw [← map_mul, ← H, hvu, map_one]
    · rw [← map_mul, ← H, huv, map_one]
  · simp

/- The kernel of a ring homomorphism is an ideal: -/
def kernel (f : R →+* S) : Ideal R where
  carrier := {r : R | f r = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add]
    rw [hb, ha, zero_add]
  zero_mem' := by
    apply map_zero
  smul_mem' := by
    intro c x hx
    simp only [smul_eq_mul, Set.mem_setOf_eq, map_mul]
    rw [hx, mul_zero]

variable (I : Ideal R) in
#check Quotient.mk (Submodule.quotientRel I)
variable (I : Ideal R) in
#check Ideal.Quotient.mk I

example (I : Ideal R) (x : R) : ⟦x⟧ = Ideal.Quotient.mk I x := by
  rfl


open RingHom Ideal.Quotient in
lemma span_equotient {I : Ideal R} (S : Set (R ⧸ I)) (x : R) (hx : ⟦x⟧ ∈ Ideal.span S) :
    x ∈ I + Ideal.span (Quotient.out '' S) := by
  rw [Ideal.span] at hx
  obtain ⟨n, ι', g', hιx⟩ := (Submodule.mem_span_set' (M := R ⧸ I)).mp hx
  -- obtain ⟨n, ι', g', hιx⟩ := (@Submodule.mem_span_set' _ (R ⧸ I) _ _ _ _ _).mp hx
  set ι : Fin n → R := fun i ↦ Quotient.out (ι' i) with hι
  set g : Fin n → Quotient.out '' S := fun i ↦ ⟨Quotient.out (g' i).val, by simp⟩ with hg
  set y : Ideal.span (Quotient.out '' S) := by
    use ∑ i, ι i • (g i)
    exact Submodule.mem_span_set'.mpr ⟨n, ι, g, rfl⟩ with hy
  replace hιx : ∑ i, ι' i * (g' i) = (mk I) x := by
    exact hιx
  have hxy : x - y ∈ I := by --restate with `mk I x` instead of `⟦x⟧`
    simp [← mk_eq_mk_iff_sub_mem, hy, ← hιx, hι, hg]
  rw [Submodule.add_eq_sup, Submodule.mem_sup]
  exact ⟨x - y, hxy, y, SetLike.coe_mem .., by abel⟩


end Rings

-- ## Exercises

noncomputable section Exercises

-- **Exercise**
-- Do you understand why the first of the next two lines compiles while the second
-- throws an error?
example (M : Type*) (α : Monoid M) : (1 : M) = (1 : M) := rfl
example (α : Type*) (M : Monoid α) : (1 : M) = (1 : M) := rfl
/- **Sol.:** The second equality does not make sense because `M` is a structure, so a collection of
many fields, not a type that can/cannot contain a term like `1`. -/

open Function

/- **¶ Exercise**
Re-experience the pain of playing with *wrongly-defined* groups. -/
lemma WrongGroup.mul_inv_cancel {α : WrongGroup} (x : α.carrier) :
    α.mul x (α.inv x) = α.one := by
  rw [← α.inv_mul_cancel (α.inv x), α.inv_eq_of_mul _ _ (α.inv_mul_cancel x)]

/- **¶ Exercise**
Why is the following example broken? Fix its statement, then prove it. -/
example (G : Type*) [Group G] (H₁ H₂ : Subgroup G) : Subgroup (H₁ ∩ H₂) := sorry
/- **Sol.:** The error comes come the fact that "being a subgroup" is not a proposition. It is the
definition of some term! A solution would be -/
example (G : Type*) [Group G] (H₁ H₂ : Subgroup G) : Subgroup (G) where
  carrier := H₁ ∩ H₂
  ...

/- **¶ Exercise**
Show that a group homomorphism is injective if and only if it has trivial kernel: even if you find a one-line
proof, try to produce the whole term. -/
example (A B : Type*) [AddGroup A] [AddGroup B] (f : A →+ B) : Injective f ↔ f.ker = ⊥ := by
    -- (f.ker_eq_bot_iff).symm
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [AddSubgroup.eq_bot_iff_forall]
    intro x hx
    apply h
    rw [hx, map_zero]
  · rw [AddSubgroup.eq_bot_iff_forall] at h
    intro x y hxy
    rw [← sub_eq_zero] at hxy ⊢
    apply h (x - y)
    rwa [AddMonoidHom.mem_ker, map_sub]



/- **¶ Exercise**
Prove that the homomorphisms between commutative monoids have a structure of commutative monoid. -/
example (M N : Type*) [CommMonoid M] [CommMonoid N] : CommMonoid (M →* N) where
  mul := by
    intro f g
    fconstructor
    · use fun x ↦ f x * g x
      simp
    · intro x y
      simp [map_mul, mul_assoc _ (f y) _, mul_comm (f y) _, ← mul_assoc]
  mul_assoc := by
    intro f g h
    ext x
    simp only [MonoidHom.mul_apply]
    exact mul_assoc ..
  one := by
    fconstructor
    · use fun _ ↦ 1
    · intro x y
      simp
  one_mul := by simp
  mul_one := by simp
  mul_comm := by
    intro f g
    ext x
    simp only [MonoidHom.mul_apply]
    exact mul_comm ..

/- **¶ Exercise**
Prove that an injective and surjective group homomorphism is an isomorphism:
but what's an isomorphism? -/
def IsoOfBijective (G H : Type*) [Group G] [Group H] (f : G →* H)
    (h_surj : Surjective f) (h_inj : Injective f) : G ≃* H := by
  set g : G ≃ H := by
    apply Equiv.ofBijective f
    simp [Bijective, h_inj, h_surj] with hg
  use g
  intro x y
  simp [hg]

/- **¶ Exercise**
Just to be sure, redo the *additive* version of something we did in class.-/
example (A : Type*) [AddCommGroup A] (N : AddSubgroup A) [N.Normal] (x y : A) :
    (x : A ⧸ N) = (y : A ⧸ N) ↔ y - x ∈ N := by simp [QuotientAddGroup.eq, sub_eq_neg_add]


/- **¶ Exercise**
Prove the claim made in class that a monoid homomorphism between groups respects the inverse. -/
example (G H : Type*) [Group G] [Group H] (f : MonoidHom_AMSS G H) (x : G) : f x⁻¹ = (f x)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv, ← f.map_mul, inv_mul_cancel, f.map_one]


/- **¶ Exercise**
Define the integers `ℤ` as a subgroup of the rationals `ℚ`: we'll see next time how to construct
(sub)sets, for the time being use `Set.range ((↑) : ℤ → ℚ)` , by copy-pasting it, as carrier. -/
example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp

/- **¶ Exercise**
State and prove that every subgroup of a commutative group is normal: even if you find a one-line
proof, try to produce the whole term. -/
example (G : Type*) [CommGroup G] (H : Subgroup G) : H.Normal where
  conj_mem x hx g := by rwa [mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  -- infer_instance
  -- exact Subgroup.normal_of_comm H


/- **¶ Exercise**
State and prove that in every additive group, the intersection of two normal subgroups is normal:
even if you find a one-line proof, try to produce the whole term. For reasons to be explained later,
the intersection is written `⊓` and types as `\inf`. -/
example (A : Type*) [AddGroup A] (H K : AddSubgroup A) :
    H.Normal → K.Normal → (H ⊓ K).Normal := by
  -- apply AddSubgroup.normal_inf_normal
  intro hH hK
  constructor
  rintro n ⟨hnH, hnK⟩ g
  exact ⟨hH.conj_mem n hnH g, hK.conj_mem n hnK g⟩


/- **¶ Exercise**
State and that the kernel of every group homomorphism is normal: even if you find a one-line proof,
try to produce the whole term. -/
example (G G₁ : Type*) [Group G] [Group G₁] (f : G →* G₁) : (f.ker).Normal := by
  -- exact MonoidHom.normal_ker f
  -- infer_instance
  constructor
  intro x hy y
  simp only [f.mem_ker, map_mul, map_inv, conj_eq_one_iff]
  rwa [← f.mem_ker]

/- **¶ Exercise**
State and that a group is commutative if and only if the map `x ↦ x⁻¹` is a group homomorphism:
even if you find a one-line proof, try to produce the whole term. To get `⁻¹`, type `\-1`. It can
be easier to split this `if and only if` statement in two declarations: are they both lemmas, both
definitions, a lemma and a definition?. -/
def inv_hom_of_comm (G : Type*) [CommGroup G] : G →* G where
  toFun := (·)⁻¹
  map_one' := by simp
  map_mul' x y := by
    simp [← mul_inv_rev, mul_comm]

def comm_of_inv_hom (G : Type*) [Group G] (f : G →* G) (hf : ∀ x, f x = x⁻¹) :
    CommGroup G where
  mul_comm g h := by
    have h1 := hf (g * h)
    rwa [mul_inv_rev, map_mul, hf, hf, inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq,
      eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul] at h1


open Subgroup in
-- **¶ Exercise**
example (G H : Type*) [Group G] [Group H] (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) :
    map φ S ≤ map φ T := by
  intro x hx
  rw [mem_map] at * -- Lean does not need this line
  rcases hx with ⟨y, hy, rfl⟩
  use y, hST hy


open Subgroup in
/- **¶ Exercise**
The whole point here is to realize that `.comp` and `∘` are morally the same, but the first is
the operation composing to group (monoid...) morphisms, the second composes two functions. -/
example (G H K : Type*) [Group G] [Group H] [Group K] (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
  ext x
  simp only [mem_map]
  constructor
  · rintro ⟨y, y_in, hy⟩
    exact ⟨φ y, ⟨y, y_in, rfl⟩, hy⟩
  · rintro ⟨y, ⟨z, z_in, hz⟩, hy⟩
    use z, z_in
    simp only [MonoidHom.coe_comp, comp_apply]
    rw [hz, hy]


open Subgroup in
/- **¶ Exercise**
For the next exercise, you might want to use the following results from the library:
`theorem Nat.card_eq_one_iff_exists : Nat.card α = 1 ↔ ∃ x : α, ∀ y : α, y = x := by ...`
as well as `eq_bot_iff_forall`, whose content you might guess... -/
lemma eq_bot_iff_card (G : Type*) [Group G] {A : Subgroup G} :
    A = ⊥ ↔ Nat.card A = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  constructor
  · intro h
    use (1 : A)
    simp [h]
  · intro H
    obtain ⟨x, hx⟩ := H
    rw [eq_bot_iff_forall]
    have hh := hx 1
    rw [← hh] at hx
    intro y hy
    specialize hx ⟨y, hy⟩
    simp only [mk_eq_one] at hx
    exact hx

/- **¶ Exercise**
Given a subgroup `B` of `A`, define the corresponding (left) setoid by hand. -/
def AddGroup_setoid {A : Type*} [AddGroup A] (B : AddSubgroup A) : Setoid A  where
  r := fun x y ↦ x - y ∈ B
  iseqv := {
    refl := by simp
    symm {x y} h := by
      rw [← neg_sub] at h
      rw [← neg_neg (y - x)]
      exact neg_mem h
    trans {x y z} h₁ h₂ := by
      rw [← sub_add_sub_cancel _ y]
      exact add_mem h₁ h₂
      }


/- **¶ Exercise**
Given two additive groups `A` and `B`, define the constant map `0` as a group homomorphism. -/
def zero_const (A B : Type*) [AddGroup A] [AddGroup B] : A →+ B where
  toFun := 0
  map_zero' := rfl
  map_add' _ _ := by simp only [Pi.zero_apply, add_zero]

/- **¶ Exercise**
State and prove that the image of an ideal through a surjective ring homomorphism is an ideal. -/
def image_ideal {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (I : Ideal R)
    (hf : Surjective f) : Ideal S where
  carrier := f.1 '' I
  add_mem' := by
    intro x y hx hy
    obtain ⟨a, ha_mem, hax⟩ := hx
    obtain ⟨b, hb_mem, hby⟩ := hy
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Set.mem_image, SetLike.mem_coe]
    use a + b
    constructor
    · apply I.add_mem
      · exact ha_mem
      · exact hb_mem
    · rw [map_add, ← hax, ← hby]
      simp
  zero_mem' := by
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Set.mem_image, SetLike.mem_coe]
    use 0
    constructor
    · apply I.zero_mem
    apply map_zero
  smul_mem' := by
    intro s x hx
    obtain ⟨a, ha_mem, hax⟩ := hx
    obtain ⟨r, hr⟩ := hf s
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, smul_eq_mul, Set.mem_image,
      SetLike.mem_coe]
    use r * a
    constructor
    · apply I.mul_mem_left
      exact ha_mem
    · rw [map_mul, hr, ← hax]
      rfl


/- **¶ Exercise**
Show that if a ring homomorphism is injective, its kernel is `⊥`. -/
example {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Injective f) :
    RingHom.ker f = ⊥ := by
  ext x
  constructor
  · intro hx
    simp only [Ideal.mem_bot]
    rw [Injective] at hf
    apply hf
    rw [hx, map_zero]
  · intro hx
    rw [Ideal.mem_bot] at hx
    rw [hx]
    exact (RingHom.ker f).zero_mem


-- **Exercise**
example {R S : Type*} [CommRing R] [CommRing S] (f : R ≃+* S) (r : R) :
    IsUnit (f r) → IsUnit r := by
  intro h
  obtain ⟨⟨v, u, hvu, huv⟩, H⟩ := h
  simp only at H
  set x := f.toEquiv.invFun u with hx
  fconstructor
  · use r
    · use x
    · apply_fun f
      rw [map_mul]
      rw [← H, hx]
      simp only [RingEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, EquivLike.apply_coe_symm_apply,
        map_one]
      exact hvu
    · apply_fun f
      rw [map_mul]
      rw [← H, hx]
      simp only [RingEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, EquivLike.apply_coe_symm_apply,
        map_one]
      exact huv
  · simp only


/- **¶ Exercise**
This is the standard fact that an ideal containing a unit is the whole ring. -/
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (r : R) :
    r ∈ I → IsUnit r → I = ⊤ := by
  intro h_mem h
  obtain ⟨⟨u, v, huv, hvu⟩, H⟩ := h
  simp only at H
  ext x
  constructor
  · intro hx
    simp only [Submodule.mem_top]
  · intro hx
    set y := r * x with hy
    have : y ∈ I := by
      rw [hy]
      rw [mul_comm]
      apply I.mul_mem_left
      exact h_mem
    apply_fun (fun t ↦ v • t) at hy
    rw [← H] at hy
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc _ u, hvu, one_mul] at hy
    rw [← hy]
    -- rw [← smul_eq_mul]
    -- apply I.smul_mem
    apply I.mul_mem_left
    exact this



open Ideal in
/- **¶ Exercise**
State and prove that every ideal in the product `A × B` of two rings (where `×` is `\x` and not `x`)
is the product of an ideal in `A` and an ideal in `B`.
*Bonus*: This is the last exercise in the file, so you might strive to get a short proof:
  mine takes one line. -/
theorem idealProd (A B : Type*) [CommRing A] [CommRing B] (J : Ideal (A × B)) :
    ∃ P : Ideal A × Ideal B, J = Ideal.prod P.1 P.2 :=
  -- ⟨⟨J.map <| RingHom.fst .., J.map <| RingHom.snd ..⟩, J.ideal_prod_eq⟩
    by
  set Ia := J.map <| RingHom.fst .. with hIa
  set Ib := J.map <| RingHom.snd .. with hIb
  use ⟨Ia, Ib⟩
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · constructor
    · apply Ideal.mem_map_of_mem
      exact hx
    · apply Ideal.mem_map_of_mem
      exact hx
  · rw [mem_prod, mem_map_iff_of_surjective _ (RingHomSurjective.is_surjective),
        mem_map_iff_of_surjective _ (RingHomSurjective.is_surjective)] at hx
    obtain ⟨⟨y, hy_mem, hyx⟩, ⟨z, hz_mem, hzx⟩⟩ := hx
    have : ⟨x.1, 0⟩ + ⟨0, x.2⟩ = x := Prod.fst_add_snd x
    rw [← this, ← hyx, ← hzx]
    simp only [RingHom.coe_fst, RingHom.coe_snd, Prod.mk_add_mk, add_zero, zero_add]
    replace hyx : ⟨y.1, y.2⟩ * ⟨1, 0⟩ = (⟨y.1, 0⟩ : A × B) := by
        calc ⟨y.1, y.2⟩ * ⟨1, 0⟩ = ⟨y.1 * 1, y.2 * 0⟩ := by rfl
                               _ = (⟨y.1, 0⟩ : A × B) := by rw [mul_one, mul_zero]
    replace hzx : ⟨z.1, z.2⟩ * ⟨0, 1⟩ = (⟨0, z.2⟩ : A × B) := by
        calc ⟨z.1, z.2⟩ * ⟨0, 1⟩ = ⟨z.1 * 0, z.2 * 1⟩ := by rfl
                                 _ = (⟨0, z.2⟩ : A × B) := by rw [mul_one, mul_zero]
    rw [← zero_add y.1, ← add_zero z.2, ← Prod.mk_add_mk 0 y.1 z.2 0, ← hzx, ← hyx, Prod.mk.eta,
        Prod.mk.eta]
    apply J.add_mem (J.mul_mem_right _ hz_mem) (J.mul_mem_right _ hy_mem)


end Exercises
