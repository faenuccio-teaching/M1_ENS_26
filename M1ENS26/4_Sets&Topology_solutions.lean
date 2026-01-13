import Mathlib.Tactic

open Set Classical


#check ∀ n : ℕ, Vector ℝ n
#check Π n : ℕ, Vector ℝ n
#check (n : ℕ) → Vector ℝ n
#check (λ n ↦ (0 : Vector ℝ n))
#check (∀ n : ℕ, n + 1 ≤ n + 2)
#check (λ n ↦ n + 1 ≤ n + 2)

#check Σ n : ℕ, Vector ℝ n
#check (n : ℕ) × Vector ℝ n
#check (⟨3, (0 : Vector ℝ 3)⟩ : (n : ℕ) × Vector ℝ n)

-- # §1: Sets

open scoped Set
section Definitions


-- **An error**
example (S : Set) := sorry
example {α : Type} (S : Set α) : S = S := by
  rfl

-- **A tautology**

example (α : Type) (x : α) (S : Set α) : x ∈ S ↔ S x := by
  rfl


-- **The positive integers**

def PositiveIntegers : Set ℤ := by
  -- intro d
  --  use if 0 < d then True else False
  -- *or* exact (fun d ↦ 0 < d)
  -- *or* exact (0 < ·) d
  exact (0 < ·)

-- `⌘`

lemma one_posint : 1 ∈ PositiveIntegers := by
  -- unfold PositiveIntegers
  -- rw [Set.mem_def]
  -- have := Nat.one_pos
  -- exact this -- *why does this fail?*
  -- rw [← Int.ofNat_lt] at this
  -- exact this
  -- *A better proof*
  exact Int.zero_lt_one

def PositiveNaturals : Set ℕ := by
  exact (0 < ·)

example : 1 ∈ PositiveNaturals := by
  -- apply one_pos -- It *fails*!
  exact Nat.zero_lt_of_ne_zero Nat.one_ne_zero

-- Why does this *fail*? How to fix it?
-- example : (-1) ∉ PositiveNaturals := sorry
/- It fails because Lean cannot be convinced that `-1 : ℕ`. The best we can do is-/
example : (-1) ∉ PositiveIntegers := by
  intro h
  replace h := h.out --not "really" needed, but sometimes useful
  -- omega -- a nice tactic that can prove these "linear (in)equalities"
  exact (Int.negSucc_not_nonneg (0 + 0).succ).mp (by exact h) --can be found by `exact?`

-- **The even naturals**

def EvenNaturals : Set ℕ := by
  -- intro d
  -- exact if d % 2 = 0 then True else False
  exact (· % 2 = 0)

example (n : ℕ) : n ∈ EvenNaturals → (n+2) ∈ EvenNaturals := by
  intro h
  replace h := h.out
  -- rw [Nat.add_mod_right]-- a pity it does not work...
  rw [mem_def]
  rw [← Nat.add_mod_right] at h -- try to comment the `replace` three lines above
  exact h


-- **An abstract set**

def AbstractSet {α : Type} (P : α → Prop) : Set α := P
def AbstractSet' {α : Type} (P : α → Prop) : Set α := setOf P

-- The same, but it is a general principle that the second version is better
example {α : Type} (P : α → Prop) : AbstractSet P = AbstractSet' P := by
  rfl


-- `⌘`


-- **Subsets as implication**
example {α : Type} (S T : Set α) (s : α) (hST : S ⊆ T) (hs : s ∈ S) : s ∈ T := by
  apply hST
  exact hs


-- `⌘`


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

-- **Another take on subsets and sets as types**

def subsub {α : Type} {S : Set α} (P : S → Prop) : Set (S : Type) := P

def subsub' {α : Type} {S : Set α} (P : α → Prop) : Set (S : Type) := by
  intro a
  exact P a

-- Are they *equal*? This is an exercise below.

-- Why does this *fail*? How to fix it?
-- example (α : Type) (S : Set α) (P : S → Prop) (x : ↑S) (hx : x ∈ subsub P) : x ∈ S := sorry
/- *Sol.:* This fails because `x` is of type `↑S`, but `S` is in `Set α`, so only terms of type `α`
can be tested for membership in `S`. It can be made to work as follows:-/
example (α : Type) (S : Set α) (P : S → Prop) (x : ↑S) (hx : x ∈ subsub P) : {s : S // P s} := by
  use x
  exact hx


-- **What is really this "injection"  `Set α ↪ Type`?**

-- Why does this *fail*? How to fix it?
-- example : ∀ n : PositiveIntegers, 0 ≤ n := sorry
/- *Sol.:*  This fails because `0` is a term of `ℕ`, whereas `n` is a term of `PositiveIntegers`.
They cannot be compared directly, because `n` is actually a *pair* of a natural number and a proof
of its positivity. It can be made to work as follows-/
example : ∀ n : PositiveIntegers, 0 < n.1 := by
  rintro ⟨-, hn⟩ --use first `rintro ⟨n, hn⟩` and then `rintro ⟨_, hn⟩`
  exact hn


-- `⌘`


/- **§ Some exercises** -/

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


-- Why does this *fail*?
-- example (α : Type) (S : Set α) : subsub = subsub' := sorry
/- *Sol.:*  Lean complains because in `subsub'` `P` is defined on the type `α` whereas in `subsub`
it is defined on the type `↑S`. So this is an equality between functions defined on different types,
that makes no sense. -/


end Definitions

-- ## Operations on sets

section Operations

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

-- `⌘`


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
    rw [lt_iff_not_le] at h_neg
    apply h_neg
    apply le_of_lt
    exact h_pos
  · intro h
    exfalso
    exact h


-- `⌘`


-- **§ Indexed unions**


example {α I : Type} (A : I → Set α) (x : α) : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := by
  -- refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  -- · rw [mem_iUnion] at h
  --   exact h
  -- · rw [mem_iUnion]
  --   exact h
  -- -- *Alternative proof*
  simp -- try also `simp?` to see what has been used


/- **§ Some exercises** -/

-- Try to prove the statement proven before but without using the library
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
    left ; exact hT
    right ; exact hR


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


-- A bit of difference, inclusion and intersection
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

end Operations


-- `⌘`


-- # §2: Functions


-- Functions do not natively act on elements of sets: how can we fix this code?
example (α β : Type) (S : Set α) (T : Set β) (f g : S → β) :
  -- f = g ↔ ∀ a : α, a ∈ S → f a  = g a := by sorry
  f = g ↔ ∀ a : α, (ha : a ∈ S) → f ⟨a, ha⟩  = g ⟨a, ha⟩ := by
  constructor
  · intro h
    rw [h]
    -- rfl -- *fails*!
    exact fun _ _ ↦ rfl -- why? Because the whole type is not an equality type.
  · intro h
    funext x
    -- exact h --why?
    apply h -- or exact h _ _


-- `⌘`


section Operations

variable (α β : Type) (f : α → β)

-- The **image**


example : 1 ∈ Nat.succ '' univ := by
  -- use 0
  -- constructor
  -- · trivial
  -- · rfl
-- *An alternative proof*
  exact ⟨0, ⟨trivial, rfl⟩⟩

-- We can upgrade a function `f` to a function between sets, using its *image*:
example : Set α → Set β := by
  intro S
  exact f '' S


example (α β: Type) (f : α → β) (S : Set α) : S ≠ ∅ → f '' S ≠ ∅ := by
  intro hS hfS
  apply hS
  rw [eq_empty_iff_forall_not_mem] at hfS ⊢
  intro x hx
  replace hfS := hfS (f x)
  apply hfS
  use x


-- `⌘`


-- The **preimage**

example : 2 ∈ Nat.succ ⁻¹' {2, 3} ∧ 1 ∉ .succ ⁻¹' {0, 3} := by
  constructor
  · rw [mem_preimage]
    trivial
  · intro h
    rw [mem_preimage] at h
    trivial


-- `⌘`

example : InjOn (fun n : ℤ ↦ n ^ 2) PositiveIntegers := by
  intro m hm n hn
  simp only
  intro H
  simp only [Int.pow_succ', Int.pow_zero, Int.mul_one] at H
  by_cases h_mlt : m < n
  · exfalso
    -- have := mul_lt_mul -- we can add a `@` before to let it compile anyhow
    -- have := @Int.mul_lt_mul -- now we see who each `a,b,c,d` must be
    have := Int.mul_lt_mul h_mlt (le_of_lt h_mlt) hm.out (le_of_lt hn.out)
    replace this := ne_of_lt this
    exact this H
  by_cases h_nlt : n < m
  · exfalso
    exact ((ne_of_lt <| Int.mul_lt_mul h_nlt (le_of_lt h_nlt) hn.out (le_of_lt hm.out))) H.symm
  exact eq_of_le_of_not_lt (le_of_not_lt h_nlt) h_mlt




/- **§ Some exercises** -/

open Function


/- The range is not *definitionally equal* to the image of the universal set:
  use extensionality! -/
example : range f = f '' univ := by
  ext x
  refine ⟨fun h ↦ ?_ , fun h ↦ ?_⟩
  · rw [mem_range] at h
    obtain ⟨y, hy⟩ := h
    use y
    constructor
    · trivial
    · exact hy
  · rw [mem_range]
    obtain ⟨y, hy⟩ := h
    use y
    exact hy.2


-- Why does this code *fail*? Fix it, and then prove the statement
-- example (N : OddNaturals) : N ∈ Nat.succ '' (EvenNaturals) :=
-- It *fails* because `N` is of the wrong type. `N.1` is a `ℕ`, and the following code compiles:
example (N : OddNaturals) : N.1 ∈ Nat.succ '' (EvenNaturals) := by
  rcases N with ⟨n, hn⟩
  have hn' := hn.out
  rw [mem_image]
  match n with
  | 0 => trivial
  | m+1 =>
    rw [Nat.succ_mod_two_eq_one_iff] at hn'
    use m
    constructor
    · exact hn'
    · exact Nat.succ_eq_add_one _


-- Why does this code *fail*? Fix it, and then prove the statement
-- example (N : OddNaturals) :  N ∈ Nat.succ ⁻¹' (EvenNaturals) := by
-- It *fails* because `N` is of the wrong type. `N.1` is a `ℕ`, and the following code compiles:
example (N : OddNaturals) :  N.1 ∈ Nat.succ ⁻¹' (EvenNaturals) := by
  rcases N with ⟨n, hn⟩
  rw [mem_preimage]
  have hn' := hn.out
  by_cases hnz : n = 0
  · rw [hnz] at hn'
    trivial
  · replace hnz := Nat.exists_eq_succ_of_ne_zero hnz
    obtain ⟨m, hm⟩ := hnz -- `obtain` combines the `Exists.choose` and `Exists.choose_spec`
    rw [hm] at hn'
    rw [Nat.succ_mod_two_eq_one_iff] at hn'
    show n.succ % 2 = 0 --`show` changes the goal to something definitionally equivalent
    omega
    -- *Alternative proof* if you forgot about `omega`:
    -- rw [hm]
    -- simp only [Nat.succ_eq_add_one]
    -- rwa [add_assoc, Nat.add_mod_right]


-- Not every `n : ℕ` is the successor or something...
example : range Nat.succ ≠ univ := by
  intro h
  rw [Set.eq_univ_iff_forall] at h
  replace h := h 0
  have := Nat.succ_ne_zero (Exists.choose h)
  exact this (Exists.choose_spec h)



/- The following is a *statement* and not merely the *definition* of being injective;
  prove it. -/
example : Injective f ↔ InjOn f univ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro a ha b hb H
    apply h H
  · intro a b H
    exact h (trivial) (trivial) H



/- With the obvious definition of surjective, prove the following result: the
 complement `Sᶜ` is referred to with the abbreviation `compl` in the library -/
example : Surjective f ↔ (range f)ᶜ = ∅ := by
  refine ⟨fun h ↦ ?_ , fun h ↦ ?_⟩
  · rw [Set.compl_empty_iff]
    ext x
    constructor
    · intro H
      trivial
    · intro H
      obtain ⟨y, hy⟩ := h x
      use y
  · intro x
    rw [Set.compl_empty_iff] at h
    rw [eq_univ_iff_forall] at h
    replace h := h x
    exact h

end Operations
