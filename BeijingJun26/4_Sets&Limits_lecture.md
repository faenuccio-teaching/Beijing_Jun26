# Sets

## Introduction
Sets are **primitive** objects when doing classical, pen-and-paper mathematics:
* no *definition*;
* only *rules* about how these objects work (unions, intersections, etc.).

That's all you need: do you ever look at $f\colon S \to T$ as $f\subseteq S\times T$?

We've seen that, for Lean, the **primitive objects** are types; yet
* sometimes we still want to speak about *sets* as collections of elements
* we want then to play the usual games.


## Definitions

+++ Every set lives in a **given** type, it is a set of elements (*terms*) in it:

    variable (α : Type) (S : Set α)

expresses that `α` is a type and `S` is a set of elements/terms of the type `α`. On the other hand,
```lean
variable (S : Set)
```
does not mean "let `S` be a set": it means nothing and it is an error.

`⌘`
+++

+++ A set coincides with the test-function defining it.

 Given a type `α`, a set `S` (of elements/terms of `α`) is a *function*
```lean
S : α → Prop
```
so `(Set α) = (α → Prop)`.

* This function is the "characteristic function" of the set `S`;
* the `a ∈ S` symbol means that the value of `S` is `True` when evaluated  at the element `a`;
* So, the positive integers are a *function*!

Yet, given a function `P : α → Prop` we prefer to write `setOf P : Set α` to denote the set, rather then `P : Set α`, to avoid _abusing definitional equality_.

### Some examples:
1. How to prove that something belongs to a set?
1. Positive naturals;
1. Even numbers;
1. An abstract set of `α` given by some `P : Prop`.

`⌘`
+++

+++ Sub(sub-sub-sub)sets are not treated as sets-inside-sets.

Given a (old-style) set $S$, what is a subset $T$ of $S$? At least two answers:
1. Another set such that $x\in T\Rightarrow x \in S$.
1. A collection of elements of $S$.

Now,
1. stresses that $T$ is a honest set satisfying some property;
1. stresses that it is a set whose elements "come from" $S$.

We take the **first approach**: being a subset is *an implication*
```lean
    variable {T S : Set α} 
    def (T ⊆ S : Prop) := ∀ a, a ∈ T → a ∈ S
```

Yet this does not answer the question "How can I *construct* a subset of a set"? The key is _upgrading_ sets 
to types: `T : Set S` for `S : Set α` means `T : Set ↑S = Set (S : Type*)`.

### Some examples:
1. Double inclusions;
1. Subsets as sets;
1. This coercion from `Set α` to `Type*`.

`⌘`
+++

## Operations on Sets
+++ **Intersection & Union**
#### **Intersection**
Given sets `S T : Set α`  have the
```lean
def (S ∩ T : Set α) := fun a ↦ a ∈ S ∧ a ∈ T
```
* Often need **extensionality**: equality of sets can be tested on elements;
* related to _functional extensionality_ : two functions are equal if and only they have if they take the same values on same arguments;
* not strange: sets *are* functions.

#### **Union**
Given sets `S T : Set α` we have the
```lean
def (S ∪ T : Set α) := fun a ↦ a ∈ S ∨ a ∈ T
```

And if `S : Set α` but `T : Set β`? **ERROR!**

`⌘`
+++

+++ **Universal & Empty set, complement and difference**

#### Universal & Empty
* The first (containing all terms of `α`) is the constant function `True : Prop`
```lean
def (univ : Set α) := fun a ↦ True
```
* The second is the constant function `False : Prop`
```lean
def (∅ : Set α) := fun a ↦ False
```
**Bonus**: There are infinitely many empty sets!

####  **Complement and Difference**
* The complement is defined by the negation of the defining property, denoted `Sᶜ`.
```lean
Sᶜ = {a : α | ¬a ∈ S}
```
The superscript `ᶜ` can be typed as `\^c`.

* The difference `S \ T : Set α`, corresponds to the property
```lean
def (S \ T : Set α) = fun a ↦ a ∈ S ∧ a ∉ T
```

`⌘`
+++

+++ **Indexed Intersections & Indexed Unions**
* One can allow for fancier indexing sets (that will actually be **types**, *ça va sans dire*): given an index type `I` and a collection `A : I → Set α`, the union `(⋃ i, A i) : Set α` consists of the union of all the sets `A i` for `i : I`.
* Similarly, `(⋂ i, A i) : Set α` is the intersection of all the sets `A i` for `i : I`.
* These symbols can be typed as `\U = ⋃` and `\I = ⋂`.

`⌘`
+++

# Filters

## Definition

A filter `F` on a type `α` is set in `Set α` (*i. e.* a collection of sets in `α`) such that:
1. The largest set `⊤ = Set.univ` is in `F`;
2. If `s,t : Set α` and `s ⊆ t`, then `s ∈ F` implies that `t ∈ F` (they are "upwards closed")
3. `F` is stable by finite intersections.

More precisely, `Filter` is a structure:

```lean
structure Filter (α : Type*) : Type*
  | sets : Set (Set α)
  | univ_sets : univ ∈ self.sets
  | sets_of_superset : ∀ {x y : Set α}, x ∈ sets → x ⊆ y → y ∈ sets
  | inter_sets : ∀ {x y : Set α}, x ∈ sets → y ∈ sets → x ∩ y ∈ sets
```

+++ Some examples of filters
* Given a term `a : α`, the collection of all sets containing `a` is the **principal** filter (at `a`): this generalises to any set `S ⊆ α`, being the case `S = {a}`. It is denoted `𝓟 S`, typed `\MCP S`.

* The collection of all sets of natural integers (or real numbers, or rational numbers...) that are
  "large enough" or "small enough" are filters. They are called `atTop` and `atBot`, respectively.

* In a topological space `X`, the collection of all neighbourhoods (*i. e.* sets containing an open neighbourhood) of a subspace `S` is a filter, denoted `𝓝 S`; when `S={x}`, we write `𝓝 x`.

`⌘`

+++

## Filters and properties

If `F : Filter ℕ` is a filter on the naturals and `P : ℕ → Prop` is a property, we might want to say that
  * `P` holds for every large enough `n` (*e.g*: satisfying $n^2 - 5 n ≥ 0$)
  * that we can find arbitrary large `n` satisfying `P` (*e.g.*: being prime).
  * We could also say that a function `f : ℝ → ℝ` satisfy `P : ℝ → Prop` "for all `x` sufficiently close to `1`" (*e.g.* being positive, when `f 1 > 0` and `f` is continuous).

+++ More generally
Given `F : Filter α` and `P : α → Prop`, we write
  * `∀ᶠ (a : α) in F, P a ↔ {a : α | P a} ∈ F`
  * `∃ᶠ (a : α) in F, P a ↔ {a : α | ¬ P a} ∉ F`
  
  and we say that `P` holds **eventually** (*resp.* **frequently**) with respect to `F`. The above cases correpond to `atTop : Filter ℕ` and `𝓝 1 : Filter ℝ`.

  * Similarly, given `f g : α → β` and `F : Filter α` we write `f =ᶠ[F] g` and we say that `f` and `g` are asymptotically equal (along `F`) if
  ```
  {a : α | f a = g a} ∈ F
  ```
+++
## Limits

Filters are (among other things) a very convenient way to talk about **convergence**.

Consider a function $f : ℝ → ℝ$ and $a,b ∈ ℝ$. To say that
$$
\lim_{x → a} f (x) = b
$$
means
$$
∀\; ε > 0, ∃\; δ > 0 \;\text{ such that }\; ‖x - a‖ < δ ⇒  ‖f(x) - b‖ < ε
$$
or, equivalently,
$$
∀\; ε > 0, ∃\; δ > 0 \;\text{ such that }\; f (a - δ, a + δ) ⊆ (b - ε, b + ε).
$$
or, equivalently, that
$$
∀\; U_b ∈ 𝓝\; b, ∃\; V_a ∈ 𝓝\; a \text{ such that }V_a ⊆ f⁻¹ U_b.
$$
Upwards-closeness of filters makes the explicit description of $V_a$ useless: to require $V_a ⊆ f^{-1}U_b$ is the same as

    ∀ U : Set ℝ, U ∈  𝓝 b → f⁻¹' U ∈ 𝓝 a



And the statement
$\displaystyle{\lim_{x → +∞} f(x)=b}$ simply becomes

    ∀ U : Set ℝ, U ∈  𝓝 b → f⁻¹' U ∈ (atTop : Filter ℝ)

+++ Is this translation really useful?

Let $f,g : ℝ → ℝ$ and $a,b,c ∈ ℝ$. One theorem is that
$$
\lim_{x → a}f (x)=b ⇒ \lim_{y → b}g(y)= c ⇒ \lim_{x → a}(g∘ f)(x)=c
$$
while
$$
\lim_{x → +∞}f (x)=b ⇒ \lim_{y → b}g(y)= c ⇒ \lim_{x → +∞}(g∘ f)(x)=c
$$
is *another* theorem, because $+∞ ∉ ℝ$. And
$$
\lim_{x → a^-}f (x)=-∞ ⇒ \lim_{y → -\infty}g(y)= c ⇒ \lim_{x → a^-}(g∘ f)(x)=c
$$
is a third one. There are (at least) **5^3=125** such theorems.
+++

+++ Filters as generalised sets

( *Recall*: elements of `𝓟 s` = all sets
containing `s`.)

* #### `𝓟 s` replaces `s`, more general filters are "generalised sets" of `α`.

1. The **order** relation: sets on `α` are
ordered by inclusion, so `S₁ ≤ S₂ ↔ S₁ ⊆ S₂ ↔ ∀ T, T ⊇ S₂ → T ⊇ S₁`. Hence:

        def le (F G : Filter α) : F ≤ G ↔ ∀ t ∈ G, t ∈ F := Iff.rfl

1. Image of a filter through a function `f : α → β`. This operation is called
`Filter.map`:

        theorem mem_map (t : Set β) (F : Filter α) : t ∈ F.map f ↔ f ⁻¹' t ∈ F := Iff.rfl

3. With all this, the statement $\displaystyle{\lim_{x → a}f(x)=L}$ becomes

       def Tendsto (f : α → β) (F : Filter α) (G : Filter β) :=
          (𝓝 a).map f ≤ (𝓝 L)

+++