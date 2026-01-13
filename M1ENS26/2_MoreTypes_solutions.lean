import Mathlib.Tactic

section Class
-- # More on Types

-- ## The hierarchy
#check ℕ
#check Type
#check Prop


-- ## Dependent types

#check ∀ n : ℕ, Vector ℝ n
#check Π n : ℕ, Vector ℝ n
#check (n : ℕ) → Vector ℝ n
#check (λ n ↦ (0 : Vector ℝ n))

#check Σ n : ℕ, Vector ℝ n
#check (n : ℕ) × Vector ℝ n
#check (⟨3, (0 : Vector ℝ 3)⟩ : (n : ℕ) × Vector ℝ n)

#check ℕ → ℝ
#check Type 3 → Type 12
#check Type 3 → Prop -- Here, `I : (Type 3 : Type 4) → (Prop : Type 0)`, with `I α = Prop` for all `α`
#check Type 31 → False -- Here, `I : Type 31 → Prop`, with `I α = False` for all `α`

universe u v
variable {A : Sort u} (I : A → Sort v)
#check (a : A) → I a
#check Σ' (a : A), I a--(a : A), I a
#check (a : A) × I a--(a : A), I a

variable {A' : Type u} (J : A' → Type v)
#check (a : A') × J a


-- Exercice
-- What is the type of `¬`?
-- It is `Prop → Prop`:
#check Not

end Class

section Exercice
-- Exercice
/- Consider the function `F` sending `n : ℕ` to the statement\
`0 ≠ n ∧ (∀ α : Type 2, ∃ v w : Vector α n), v ≠ w`)
1. How do you expect `F 2` to look like?
2. What is the type of `fun n ↦ ((fun α : Type 2) ↦ ∃ v : Vector α n, v ≠ 0`?
3. What is the type of `fun n ↦ (∀ α : Type 2, ∃ v : Vector α n, v ≠ 0)`? To which universe level
  does this type belong to?
4. What is the type of `F 2`, and to which universe level does this type belong?
5. Is `F 2` true?
6. What is the type of `F` and to which universe level does this type belong?
-/

-- *1.* `F 2` should be a pair of a proof that `0 ≠ 2` and of the existence of a non-zero
-- 2-dimensional vector for every `v`.
-- *2.* The type of `fun (n : ℕ) ↦ (fun (α : Type 2) ↦ ∃ (v w : Vector α n), v ≠ w)` is `ℕ → Type 2 → Prop`
-- *3.* The type of `fun (n : ℕ) ↦ (∀ α : Type 2, ∃ (v w : Vector α n), v ≠ w)` is `ℕ → Prop`, which
-- is of universe level `Type 0` since both `ℕ` and `Prop` are terms in `Type 0`.
-- *4.* The type of `F 2` is a `Prop`, which is of universe level `Type 0`.
-- *5.* No, it is false: among all types in `Type 2` there is the empty type, for which it is
-- impossible to find two different 2-dimensional vectors.
-- *6.* `F` is of type `ℕ ↦ Prop`, of level `Type 0`.


-- # §3 : Inductive types

section InductiveTypes

inductive NiceType : Type
  | Tom : NiceType
  | Jerry : NiceType
  | f : NiceType → NiceType
  | g : ℕ → NiceType → NiceType → NiceType
open NiceType

#check NiceType
#check f (g 37 Tom Tom)

inductive ENS_Nat
| ENS_zero : ENS_Nat
| ENS_succ : ENS_Nat → ENS_Nat
open ENS_Nat

#print ENS_Nat
#check ENS_Nat

-- We want to prove that `ENS_Nat = ℕ`: they are *constructed* in the same way!
def JustOne_fun : ℕ → ENS_Nat
  | 0 => ENS_zero
  | Nat.succ m => ENS_succ (JustOne_fun m)


--This we leave as an exercise...
def JustOne_inv : ENS_Nat → ℕ
  | ENS_zero => 0
  | ENS_succ a => Nat.succ (JustOne_inv a)

def JustOne_Left : LeftInverse JustOne_inv JustOne_fun := by
  intro n
  induction' n with m hm
  · rfl
  · rw [JustOne_fun, JustOne_inv, hm]
  -- *Alternative, **recursive**, proof*, without induction
  -- match n with
  -- | 0 => rfl
  -- | Nat.succ m =>
  --     rw [JustOne_fun, JustOne_inv, JustOne_Left]

--This we leave as an exercise...
def JustOne_Right : RightInverse JustOne_inv JustOne_fun
  | ENS_zero => rfl
  | ENS_succ m => by rw [JustOne_inv, JustOne_fun, JustOne_Right]


def JustOne : ℕ ≃ ENS_Nat where
  toFun := JustOne_fun
  invFun := JustOne_inv
  left_inv := JustOne_Left
  right_inv := JustOne_Right


inductive ENS_Or (p q : Prop) : Prop
| left : p → ENS_Or p q
| right : q → ENS_Or p q

#print ENS_Or

example (n : ENS_Nat) : ENS_Or (n = ENS_zero) (∃ m, n = ENS_succ m) := by
  cases' n with m -- this is a case-splitting on the way an `ENS_succ` can be constructed
  · apply ENS_Or.left
    rfl
  · apply ENS_Or.right
    cases' m with d
    · use ENS_zero
    · use ENS_succ d




/- **§ Some exercises** -/



-- **1** : Fill in the `sorry` in `JustOne_inv` and in `JustOne_Right`.
-- *Solutions* are above

-- **2** The successor is not surjective, but you can't rely on the library this time.
example : ¬ Surjective ENS_succ := by
  intro habs
  obtain ⟨a, ha⟩ := habs ENS_zero
  cases ha

/- **3** Define an inductive type `Politics` with two terms : `Right` and `Left`-/
inductive Politics
  | Right : Politics
  | Left : Politics


-- leave this line as it is
open Politics

/- **4** Define a function `swap : Politics → Politics` sending `Right` to `Left` and viceversa-/
def swap : Politics → Politics
  | Right => Left
  | Left => Right

/- **5** Prove that if someone is not on the `Right`, they are on the `Left` -/
example (a : Politics) : a ≠ Right → a = Left := by
  intro ha
  cases a
  · exfalso
    trivial
  · rfl

end InductiveTypes

-- # §4 : Inductive families

section InductiveFamilies

inductive NiceProp : Prop
  | Tom : NiceProp
  | Jerry : NiceProp
  | f : NiceProp → NiceProp
  | g : ℕ → NiceProp → NiceProp → NiceProp

#check NiceProp


inductive NiceFamily : ℕ → Prop
  | Tom : NiceFamily 0
  | Jerry : NiceFamily 1
  | F : ∀n : ℕ, NiceFamily n → NiceFamily (n + 37)
  | G (n : ℕ) : ℕ → NiceFamily n → NiceFamily (n + 1) → NiceFamily (n + 3)

#check NiceFamily
#check NiceFamily 2
#check NiceFamily 21
#print NiceFamily

-- # §4 : Inductive predicates

inductive IsEven : ℕ → Prop
  | zero_even : IsEven 0
  | succ_succ (n : ℕ) : IsEven n → IsEven (n+2)


example : IsEven 4 := by
  apply IsEven.succ_succ
  apply IsEven.succ_succ
  -- *Alternative proof* repeat apply IsEven.succ_succ
  exact IsEven.zero_even

example : ¬ IsEven 5 := by
  intro h
  cases h with
  | succ_succ n hn =>
    cases hn with
    | succ_succ m hm =>
      cases hm

lemma not_isEven_succ_succ (n : ℕ) : ¬ IsEven n ↔ ¬ IsEven (n + 2) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro hf
    cases hf
    trivial
  · intro hf
    have := IsEven.succ_succ n hf
    trivial

lemma not_IsEven_succ : ∀ n : ℕ, IsEven n ↔ ¬ IsEven (n + 1) := by
  intro n
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with _ | ⟨n, hn⟩ -- what are the new cases? how many? why?
    · intro hf
      cases hf
    · intro hf
      rcases hf with _ | ⟨-, H⟩
      exact (not_IsEven_succ n).mp hn H
  · induction' n with d hd
    · exact IsEven.zero_even
    · rw [← not_isEven_succ_succ] at h
      replace hd := hd.mt
      simp only [Decidable.not_not] at hd
      apply hd
      exact h




/- **§ Some exercises** -/



-- **1** Recall the `repeat` tactic
example : ¬ IsEven 111 := by
  intro h
  repeat rcases h with _ | ⟨-, h⟩


-- Let's consider the *set* of even numbers satisfying `IsEven`
abbrev Evens := setOf IsEven

/- **2** Show that the two set of even numbers we defined are actually the same.
To translate `IsEven d` into `d ∈ Even` you can use `mem_setOf_eq`. -/
lemma EvenEq (n : ℕ) : n ∈ EvenNaturals ↔ n ∈ Evens := by
  induction' n with m h_ind
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · exact IsEven.zero_even
    · trivial--rfl -- notice the difference!
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [mem_setOf_eq, not_IsEven_succ]
      replace h : (m + 1) % 2 = 0 := h.out
      replace h : m % 2 = 1 := by
        rwa [Nat.succ_mod_two_eq_zero_iff] at h
      replace h : m ∉ EvenNaturals := by
        intro hm
        replace hm := hm.out
        rw [hm] at h
        exact zero_ne_one h
      replace h_ind : ¬ IsEven m := (h_ind.mpr).mt h
      rcases m with _ | ⟨n, hn⟩
      · exfalso
        apply h
        rfl
      · intro h
        rcases h with _ | ⟨-, h⟩
        cases h
      · rwa [Nat.add_assoc, ← not_isEven_succ_succ]
    · rw [mem_setOf_eq, not_IsEven_succ] at h
      replace h : ¬ IsEven m := by
        intro h
        replace h := h.succ_succ
        trivial
      replace h_ind := h_ind.mp.mt h
      replace h_ind : ¬ m % 2 = 0 := h_ind
      rw [Nat.mod_two_ne_zero] at h_ind
      rw [← Nat.succ_mod_two_eq_zero_iff] at h_ind
      exact h_ind

-- **3** Prove that every even number can be divided by `2`.
lemma exists_half (n : Evens) : ∃ d : ℕ, n = 2 * d := by
  have hn := n.2
  replace hn : n.1 % 2 = 0 := by
    rwa [← EvenEq] at hn
  replace hn := Nat.dvd_of_mod_eq_zero hn
  exact ⟨hn.choose, hn.choose_spec⟩

noncomputable
def half : Evens → (univ : Set ℕ) := fun n ↦ ⟨(exists_half n).choose, trivial⟩

-- **4** Doubling and halving is the identity.
lemma double_half (n : Evens) : n = 2 * (half n).1 := by
  exact (exists_half n).choose_spec

-- **5** Some more fun with functions.
example : InjOn half univ := by
  rintro ⟨n, hn⟩ - ⟨m, hm⟩ - h
  simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq]
  have hhn := double_half ⟨n, hn⟩
  rw [h, ← double_half] at hhn
  exact hhn

-- **6** Even more fun!
example : Surjective half := by
  rintro ⟨n, -⟩
  have hn : 2 * n ∈ Evens := by
    rw [← EvenEq]
    show 2 * n % 2 = 0
    omega
  let a : Evens := ⟨2 * n , hn⟩
  use a
  have := double_half a
  rw [Nat.mul_right_inj] at this
  rw [this]
  omega


end InductiveFamilies
