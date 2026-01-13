
# Functions

## Introduction

Functions among types are *primitive notions*: given two types `α` and `β`, the type `α → β` exists
as a type *axiomatically*. And there is a rule saying

    a : α, f : α → β ⊢ f a : β

that can be read
1. If the type of `a` is `α` and the type of `f` is `α → β`, then the expression `f a` has a meaning, and it is a term of type `β`.
1. `f` behaves like a function from `α` to `β`, sending `a` to `f a`.


Sometimes we want to speak about functions among *sets* : **functions among sets are different gadgets than functions among types**.

Let's inspect the following code:
```lean
example (α β : Type) (S : Set α) (T : Set β) (f g : S → T) :
    f = g ↔ ∀ a : α, a ∈ S → f a = g a :=
```
It *seems* to say that `f = g` if and only if they coincide on every element of the domain, yet... `⌘`

+++ Take-home message
To apply `f : α → β` to some `s ∈ S : Set α`, *restrict* it to the *subtype* `↑S` attached to `S`.

+++

## Operations

Given a function `f : α → β` and sets `(S : Set α), (T : Set β)`, there are some constructions and properties that we are going to study:

+++ The **image** of `S` through `f`, noted `f '' S`.
This is the *set* `f '' S : Set β` whose defining property is
```lean
f '' S := fun b ↦ ∃ x, x ∈ S ∧ f x = b
```
Unfortunately it comes with a lot of accents (but we're in France...): and with a space between `f` and `''`: it is not `f'' S`, it is `f '' S`.



`⌘`
+++

+++ The **range** of `f`, equivalent to `f '' univ`.
I write *equivalent* because the defining property is
```lean
range f := (fun b ↦ ∃ x, f x = b) : β → Prop = (Set β)
```
This is not the verbatim definition of `f '' univ` : there will be an exercise about this.
+++

+++ The **preimage** of `T` through `f`, denoted `f ⁻¹' T`.
This is the set
```lean
f ⁻¹' T : Set α := fun a ↦ f a ∈ T
```
This also comes with one accent and _two_ spaces; the symbol `⁻¹` can be typed as `\^-1`.

`⌘`
+++

+++ The function `f` is **injective on `S`**, denoted by `InjOn f S` if it is injective (a notion defined for functions **between two types**) when restricted to `S`:
```lean
def : InjOn f S := ∀ x₁ ∈ S, ∀ x₂ ∈ S, f x₁ = f x₂ → x₁ = x₂
```

In particular, the following equivalence is not a tautology:
```lean
example : Injective f ↔ InjOn f univ
```
rather, it will be an exercise for you.

The obvious definition of *surjectivity* is also available...

`⌘`

+++
