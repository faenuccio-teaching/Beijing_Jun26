import Mathlib


-- ## Painful examples

example {G : Type*} [Group G] (g e : G) (h : g * e = g) : e = 1 := by
  calc e = 1 * e := sorry

example {G : Type*} [CommGroup G] (N : Subgroup G) : CommGroup (G ⧸ N) := sorry

/- Can you understand the error message (I'm not asking whether you understand *why* you get
and error: just what it says). -/
lemma quotComm_lemma {G : Type*} [Group G] (N : Subgroup G) : CommGroup (G ⧸ N) := by sorry

-- This is false, but at least it compiles
def quotComm_def {G : Type*} [Group G] (N : Subgroup G) : Group (G ⧸ N) := by sorry


lemma unit_surj (A B : Type*) [CommRing A] [CommRing B] {f : A →+* B} (a : Aˣ) : IsUnit (f a) := by
  sorry

-- `⌘`

noncomputable section Groups

-- ### A wrong way to define structures

structure WrongGroup where
  carrier : Type*
  one : carrier
  mul : carrier → carrier → carrier
  inv : carrier → carrier
  mul_one : ∀ (x : carrier), mul x one = x
  one_mul : ∀ (x : carrier), mul one x = x
  mul_assoc : ∀ (x y z : carrier), mul (mul x y) z = mul x (mul y z)
  inv_mul_cancel : ∀ (x : carrier), mul (inv x) x = one

lemma WrongGroup.inv_eq_of_mul {α : WrongGroup} (x y : α) :
    α.mul x y = α.one → α.inv x = y := sorry

structure WrongSemigroup where
  carrier : Type*
  mul : carrier → carrier → carrier
  mul_assoc : ∀ (x y z : carrier), mul (mul x y) z = mul x (mul y z)


lemma assoc_mul (X : WrongSemigroup) (x y z w : X.carrier) :
    X.mul x (X.mul (X.mul y z) w) = X.mul (X.mul x y) (X.mul z w) := sorry

lemma assoc_mul' (G : WrongGroup) (x y z w : G.carrier) :
    G.mul x (G.mul (G.mul y z) w) = G.mul (G.mul x y) (G.mul z w) := sorry

def Nplus : WrongSemigroup := sorry

example : Nplus.mul 1 1 = 2 := rfl

-- `⌘`

-- ### A good way to define structures

#print Group
-- and right-clicking on it yields (the `_at_ENS` avoids Lean complaining this already exists)
structure Group_at_ENS (G : Type*) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

#print DivInvMonoid

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := sorry

#print CommGroup
-- and right-clicking on it yields
structure CommGroup_at_ENS (G : Type*) extends Group G, CommMonoid G

example {G : Type*} [CommGroup G] (x y : G) : (x * y)⁻¹ = x⁻¹ * y⁻¹ := sorry

example {A : Type*} [AddCommGroup A] (x y : A) : x + y + 0 = x + y := by
  sorry

lemma mul_square {G : Type*} [Group G] {x y : G} (h : x * y = 1) : x * y ^ 2 = y := sorry

-- actually `mul_assoc` does not only work for groups.
#check mul_assoc

-- `⌘`

-- ## Classes

example {A : Type*} [AddGroup A] (x y : A) : x + y + 0 = x + y := sorry

#print HAdd
-- @[inherit_doc] infixl:65 " + "   => HAdd.hAdd

#synth Group ℤ
#synth AddGroup ℤ
#synth AddGroup (ℤ × ℤ)

#print One
#synth One ℤ

example : AddGroup (ℤ × ℚ) := inferInstance

example {A : Type*} [AddGroup A] {a b : A} (h : a + b = 0) : a + 2 • b = b := sorry

-- What's going on here?
example (G : Type*) [Group G] [CommGroup G] (g : G) : 1 * g = g := by
  rw [one_mul]

-- #### The `Coe` class
#check Complex.exp_add_pi_mul_I (3/2 : ℚ)
#print RatCast
#synth RatCast ℂ

instance : Coe WrongGroup Type := sorry


example {α : WrongGroup} (x : α) :
    α.mul x (α.inv x) = α.one := sorry

instance : Add Bool where
  add b₁ b₂ := b₁ && b₂

example : true + false = false := sorry

-- `⌘`

-- ### More about groups

variable (G : Type*) [Group G]

-- #### Subgroups
example (H : Subgroup G) : Group H := sorry

variable (H : Subgroup G) in
#synth Group H


/- We have an automatic coercion from sets to types (more about this in the next class),
so we get a coercion from subgroups to types: -/
example (H : Subgroup G) (x : H) (hx : x = 1) : (x : G) = 1 := sorry

example (H : Subgroup G) : 1 ∈ H := sorry

/- Observe what happens if one writes

  `AddSubgroup ℤ :=`
  `_`

-/
example : AddSubgroup ℤ := sorry


/- In the example below, note two things:
1. What happens if we remove `Comm`;
2. What happens to the `G` and `Group G` that are globally defined in this section;
-/
example (G : Type*) [CommGroup G] (H₁ H₂ : Subgroup G) {x y : G} (hx : x ∈ H₁) (hy : y ∈ H₂) :
    x * y ∈ H₁ ⊔ H₂ := sorry

example (x : G) (hx : x ∈ (⊥ : Subgroup G)) : x = 1 := sorry



example : (Subgroup.center G).Normal := sorry

-- `⌘`

-- #### Homomorphisms


structure MonoidHom_ENS (M N : Type*) [Monoid M] [Monoid N] where
  toFun : M → N
  map_one : toFun 1 = 1
  map_mul : ∀ (x y : M), toFun (x * y) = (toFun x) * (toFun y)



example (G H : Type*) [Group G] [Group H] (f g : MonoidHom_ENS G H)
    (H : ∀ x, f.toFun x = g.1 x) : f = g := by -- the `f.toFun` and `g.1` are horrible!
  sorry

#check MonoidHom.ext

def f : MonoidHom_ENS (ℕ × ℕ) ℕ := sorry

#check f ⟨2,3⟩ -- we can't apply a `MonoidHom₁` to an element, which is annoying


#check f.toFun ⟨2,3⟩
#eval f.toFun ⟨2,3⟩

/- We would like to able to write `f ⟨2,3⟩` instead of `f.toFun ⟨2,3⟩`. We do this
using the `CoeFun` class, which is a class for objects that can be coerced into
functions.-/

#print CoeFun


instance {G H : Type*} [Monoid G] [Monoid H] :
    CoeFun (MonoidHom_ENS G H) (fun _ ↦ G → H) where
  coe := MonoidHom_ENS.toFun

-- attribute [coe] MonoidHom_ENS.toFun
#check f ⟨2,3⟩

example (G₁ : Type) [CommGroup G₁] (f : G →* G₁) : ∀ x y : G, x * y = 1 → (f x) * (f y) = 1 :=
  sorry


example (A : Type*) [AddGroup A] (f : G →* A) : ∀ x y : G, x * y = 1 → (f x) * (f y) = 1 := by sorry

open Function in
example (A : Type*) [AddGroup A] (f : A →+ ℤ) (hf : 1 ∈ f.range) : Surjective f := sorry


-- `⌘`

-- #### Quotients

#print Setoid
#print Equivalence
#print Quotient

variable (H : Subgroup G)

#print QuotientGroup.leftRel
#check QuotientGroup.leftRel H
#check (QuotientGroup.mk' _ : [_? : H.Normal] → G →* G ⧸ H)


example (N : Subgroup G) [N.Normal] (x y : G) : (x : G ⧸ N) = (y : G ⧸ N) ↔ x * y⁻¹ ∈ N :=
  sorry

/- Class type inference makes Lean understand that since `H` is
commutative, `N` is normal and thus `H ⧸ N` is a group. -/
example (H : Type*) [CommGroup H] (f : H →* G) (N : Subgroup H) (hN : N ≤ f.ker) :
    {g : H ⧸ N →* G // ∀ h : H, f h = g h } := sorry


example [H.Normal] (K : Subgroup G) : Subgroup (G ⧸ H) where
  carrier := sorry
  one_mem' := sorry
  mul_mem' := sorry
  inv_mem' := sorry

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

example (a b c : ℚ) : a + (b + c * 1) = a + b + c := sorry


#check mul_one
#check add_assoc
#print AddMonoid
#print Field
#print IsDomain
#print CommMonoid


example (R : Type*) [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := sorry


lemma sixth_pow (R : Type*) [CommRing R] (x y : R) : (x + y) ^ 6 =
    x ^ 6 + 6 * x ^ 5 * y +  15 * x ^ 4 * y ^ 2 + 20 * x ^ 3 * y ^ 3 +
      15 * x ^ 2 * y ^ 4 + 6 * x * y ^ 5 + y ^ 6 := sorry

#print axioms sixth_pow

example (R : Type*) [CommRing R] (x y : R) (H : x ^ 2 ≠ y ^ 2) : x ≠ y := sorry


variable {R S : Type*} [CommRing R] [CommRing S]

example (f : R →+* S) (r : R) : IsUnit r → IsUnit (f r) := by
  sorry

/- The kernel of a ring homomorphism is an ideal: -/
def kernel (f : R →+* S) : Ideal R := sorry


variable (I : Ideal R) in
#check Quotient.mk (Submodule.quotientRel I)
variable (I : Ideal R) in
#check Ideal.Quotient.mk I

example (I : Ideal R) (x : R) : ⟦x⟧ = Ideal.Quotient.mk I x := sorry


open RingHom Ideal.Quotient in
lemma span_equotient {I : Ideal R} (S : Set (R ⧸ I)) (x : R) (hx : ⟦x⟧ ∈ Ideal.span S) :
    x ∈ I + Ideal.span (Quotient.out '' S) := by
  sorry


end Rings

-- ## Exercises

noncomputable section Exercises

open Function

/- **¶ Exercise**
Re-experience the pain of playing with *wrongly-defined* groups. -/
lemma WrongGroup.mul_inv_cancel {α : WrongGroup} (x : α.carrier) :
    α.mul x (α.inv x) = α.one := sorry

/- **¶ Exercise**
Why is the following example broken? Fix its statement, then prove it. -/
example (G : Type*) [Group G] (H₁ H₂ : Subgroup G) : Subgroup (H₁ ∩ H₂) := sorry

/- **¶ Exercise**
Show that a group homomorphism is injective if and only if it has trivial kernel: even if you find a one-line
proof, try to produce the whole term. -/
example (A B : Type*) [AddGroup A] [AddGroup B] (f : A →+ B) : Injective f ↔ f.ker = ⊥ := sorry

/- **¶ Exercise**
Prove that the homomorphisms between commutative monoids have a structure of commutative monoid. -/
example (M N : Type*) [CommMonoid M] [CommMonoid N] : CommMonoid (M →* N) := sorry

/- **¶ Exercise**
Prove that an injective and surjective group homomorphism is an isomorphism:
but what's an isomorphism? -/
def IsoOfBijective (G H : Type*) [Group G] [Group H] (f : G →* H)
    (h_surj : Surjective f) (h_inj : Injective f) : G ≃* H := sorry

/- **¶ Exercise**
Just to be sure, redo the *additive* version of something we did in class.-/
example (A : Type*) [AddCommGroup A] (N : AddSubgroup A) [N.Normal] (x y : A) :
    (x : A ⧸ N) = (y : A ⧸ N) ↔ y - x ∈ N := sorry


/- **¶ Exercise**
Prove the claim made in class that a monoid homomorphism between groups respects the inverse. -/
example (G H : Type*) [Group G] [Group H] (f : MonoidHom_ENS G H) (x : G) : f x⁻¹ = (f x)⁻¹ :=
  sorry


/- **¶ Exercise**
Define the integers `ℤ` as a subgroup of the rationals `ℚ`: we'll see next time how to construct
(sub)sets, for the time being use `Set.range ((↑) : ℤ → ℚ)` , by copy-pasting it, as carrier. -/
example : AddSubgroup ℚ := sorry

/- **¶ Exercise**
State and prove that every subgroup of a commutative group is normal: even if you find a one-line
proof, try to produce the whole term. -/


/- **¶ Exercise**
State and prove that in every additive group, the intersection of two normal subgroups is normal:
even if you find a one-line proof, try to produce the whole term. For reasons to be explained later,
the intersection is written `⊓` and types as `\inf`. -/



/- **¶ Exercise**
State and that the kernel of every group homomorphism is normal: even if you find a one-line proof,
try to produce the whole term. -/



/- **¶ Exercise**
State and that a group is commutative if and only if the map `x ↦ x⁻¹` is a group homomorphism:
even if you find a one-line proof, try to produce the whole term. To get `⁻¹`, type `\-1`. It can
be easier to split this `if and only if` statement in two declarations: are they both lemmas, both
definitions, a lemma and a definition?. -/


open Subgroup in
-- **¶ Exercise**
example (G H : Type*) [Group G] [Group H] (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) :
    map φ S ≤ map φ T := sorry


open Subgroup in
/- **¶ Exercise**
The whole point here is to realize that `.comp` and `∘` are morally the same, but the first is
the operation composing to group (monoid...) morphisms, the second composes two functions. -/
example (G H K : Type*) [Group G] [Group H] [Group K] (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := sorry


open Subgroup in
/- **¶ Exercise**
For the next exercise, you might want to use the following results from the library:
`theorem Nat.card_eq_one_iff_exists : Nat.card α = 1 ↔ ∃ x : α, ∀ y : α, y = x := by ...`
as well as `eq_bot_iff_forall`, whose content you might guess... -/
lemma eq_bot_iff_card (G : Type*) [Group G] {A : Subgroup G} :
    A = ⊥ ↔ Nat.card A = 1 := sorry

/- **¶ Exercise**
Given a subgroup `B` of `A`, define the corresponding (left) setoid by hand. -/
def AddGroup_setoid {A : Type*} [AddGroup A] (B : AddSubgroup A) : Setoid A  := sorry

/- **¶ Exercise**
Given two additive groups `A` and `B`, define the constant map `0` as a group homomorphism. -/

/- **¶ Exercise**
State and prove that the image of an ideal through a surjective ring homomorphism is an ideal. -/


/- **¶ Exercise**
Show that if a ring homomorphism is injective, its kernel is `⊥`. -/
example {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Injective f) :
    RingHom.ker f = ⊥ := sorry


-- **Exercise**
example {R S : Type*} [CommRing R] [CommRing S] (f : R ≃+* S) (r : R) :
    IsUnit (f r) → IsUnit r := sorry


/- **¶ Exercise**
This is the standard fact that an ideal containing a unit is the whole ring. -/
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (r : R) :
    r ∈ I → IsUnit r → I = ⊤ := sorry



open Ideal in
/- **¶ Exercise**
State and prove that every ideal in the product `A × B` of two rings (where `×` is `\x` and not `x`)
is the product of an ideal in `A` and an ideal in `B`.
*Bonus*: This is the last exercise in the file, so you might strive to get a short proof:
  mine takes one line. -/
theorem idealProd (A B : Type*) [CommRing A] [CommRing B] (J : Ideal (A × B)) :
    ∃ P : Ideal A × Ideal B, J = Ideal.prod P.1 P.2 := sorry


end Exercises
