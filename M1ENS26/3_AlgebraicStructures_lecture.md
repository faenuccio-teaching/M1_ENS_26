# Algebraic Structures

Let's begin with some *painful* example: `⌘`

## Groups

1. A bad definition (with all fields)

1. A better one (extending `Monoid`) 


    Mathlib chose the second solution, because this way we can put a group structure
    on an already defined type, such as `ℤ` or `Equiv α α`. Things will differ when we define the 
    category of groups, its objects being terms of a type resembling the "bad" definition.

`⌘`

1. Mathlib and its doc **[ToDo]**
### Interlude: Classes and Class Inference
+++ Some automation we’ve just witnessed
1. Lean was able to "automatically" decide to use `1` and `*` for `G : Group` or `G : CommGroup`,
and to use `0` and `+` for `A : AddGroup` or `A : AddCommGroup`.
1. If we inspect `mul_assoc` we see
    ```
    mul_assoc {G : Type*} [Semigroup G] (a b c : G) : a * b * c = a * (b * c)
    ```
but we used it for a group: Lean understood that every group is a semigroup.
1. The use of `extend` to define `Group`, yielding an "enriched" `DivInvMonoid`.
1. Some redundancy in the definition of `Group` (of `Monoid`, actually) concerning `npow : ℕ → M → M`.
+++
Most of the above points are related to *classes* and *class type inference*.

1. Discuss what classes are, what inference is, what `[` and `]` are, what instances are
1. Discuss `#synth` 
1. Make examples of instances: beyond notation, start with `Coe` (and `CoeSort`); then go back to "every group is a monoid" and the quotcommlemma.
### More about groups
#### Subgroups
The definition of subgroups is slightly different from that of a group, it relies on `Sets`:
```
structure Subgroup (G : Type* u_3*) [Group G] extends Submonoid G : Type*

A subgroup of a group G is a subset containing 1, closed under multiplication and closed under multiplicative inverse.

    carrier : Set G
    mul_mem' {a b : G} : a ∈ self.carrier → b ∈ self.carrier → a * b ∈ self.carrier
    one_mem' : 1 ∈ self.carrier
    inv_mem' {x : G} : x ∈ self.carrier → x⁻¹ ∈ self.carrier
```
We'll discuss what "sets" are next time, but for now just observe that given any type `G : Type*`, 
and any set `S : Set G`, we obtain for every `g : G` the type (of kind `Prop`) `g ∈ S`, that can be either true or false.

Observe in particular, as we've discussed for monoids, that "being a subgroup" is not a `Prop`-like
notion: the perspective is that, to each group `G`, we attach a new *type* `Subgroup G` whose terms
represent the different subgroups of `G`, seen as an underlying set and a collection of proofs that
the set is multiplicatively closed (a "mixin").

1. Another example of instance: every subgroup is a group
1. Coe, norm_num e norm_cast

#### [Quotients](https://github.com/faenuccio-teaching/M2Lyon2425/blob/afcb059590adbe169d3e03ce50277ef920a9b567/M2Lyon2425/Groups2_solutions.lean#L465)


#### Morphisms
## Rings
1. Def, Ideals, `CommRing`, `IsDomain`  
2. `grind`, `ring`
3. `#synth CommRing ℤ`
4. [Units](https://github.com/faenuccio-teaching/M2Lyon2425/blob/afcb059590adbe169d3e03ce50277ef920a9b567/M2Lyon2425/Rings1_solutions.lean#L127)
5. [Ring Homs](https://github.com/faenuccio-teaching/M2Lyon2425/blob/afcb059590adbe169d3e03ce50277ef920a9b567/M2Lyon2425/Rings1_solutions.lean#L173)