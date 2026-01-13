import Mathlib.Tactic

variable (P Q R S : Prop)
open Polynomial

-- **ToDo**
example (n : ℕ) (hn : n ≤ 3) : n ≤ 5 := by
  apply le_trans
  use hn
  linarith


-- `⌘`


/- # exact, intro, apply, rfl-/

-- Use of the `exact` tactic
-- **ToDo**
example (hP : P) : P := by
  exact hP

-- Use of the `intro` tactic
-- **ToDo**
example : P → P := by
  intro hP
  exact hP

-- Use of the `apply` tactic
-- **ToDo**
example (h : P → Q) (hP : P) : Q := by
  apply h
  exact hP

-- Use `\.` to write `·`
-- **ToDo**
example : (P → Q → R) → ((P → Q) → (P → R)) := by
  intro h1
  intro h2
  intro hP
  apply h1
  · exact hP
  · apply h2
    exact hP


-- Use of the `rfl` tactic
-- **ToDo**
example : P = P := by
  rfl

-- **ToDo**
example : 3 = 2 + 1 := by
  rfl

-- `⌘`

-- # `rw`

-- `P` is not a proposition: it is a True/False statement for terms in `α`.
-- **ToDo**
example (α : Type) (P : α → Prop) (x y : α) (hx : P x) (h : y = x) : P y := by
  rw [h]
  exact hx


-- **ToDo**
example (α : Type) (P Q : α → Prop) (x : α) (hP : P x) (h : P = Q) : Q x := by
  rw [← h] -- Use `\l` to write `←`
  exact hP

-- **ToDo**
example (α : Type) (P Q : α → Prop) (x : α) (hP : P x) (h : P = Q) : Q x := by
  rw [h] at hP
  exact hP


-- `⌘`

/- # Conjunction / And
  Use `\and` to write `∧` -/

-- **ToDo**
example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  · exact hP
  · exact hQ

-- **ToDo**
example : P ∧ Q → P := by
  intro h
  exact h.left

/-  # Disjunction / Or
  Use `\or` to write `∨` -/

-- **ToDo**
example : P → P ∨ Q := by
  intro hP
  left
  exact hP

/- **ToDo**
  symmetry of `∨`, and use of `assumption`  -/
example : P ∨ Q → Q ∨ P := by
  intro h
  cases h
  · right
    assumption
  · left
    assumption

/- **ToDO**
   the result of `cases` can be given explicit names, by using `rcases ? with ?1 | ?h2 `-/
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h1 h2 h3
  rcases h1 with h | h
  · apply h2
    exact h
  · apply h3
    exact h

/- **ToDO**
  use of the `by_cases` tactic. -/
example : R ∨ ¬ R := by
  by_cases hR : R
  · left
    exact hR
  · right
    exact hR

-- `⌘`

/- # Types -/

#check 2
#check ℕ
#check (2 : ℤ)
#check 2 < 3
#check (∀ n : ℕ, ∀ x y z : ℤ, 2 < n → x ^ n + y ^ n = z ^ n → x*y*z = 0)
#check Real.sin
#check (Real.sin : ℝ → ℝ)

-- **ToDo**
example : (1 : ℕ) = (1 : ℝ) := rfl
-- **ToDo**
example : 1 = (1 : ℚ) := rfl
-- **ToDo**
example : (1 : ℚ) = (1 : ℚ[X]):= rfl

-- `⌘`

/- ## Prop types -/

#check 37 < 1
#check True
#check False
#check trivial
#check true
#check false
#check Bool


-- `⌘`

/- # Exercises -/

-- Modus Ponens: if `P → Q` then `Q` can be deduced from `P`
-- **Exercise**
example : P → (P → Q) → Q := by
  intro hP h
  apply h
  exact hP


-- Transitivity of `→`
-- **Exercise**
example : (P → Q) → (Q → R) → P → R := by
  intro h1 h2 hP
  apply h2
  apply h1
  exact hP

-- **Exercise**
example (hP : P) : Q → (hP = hP) := by
  intro
  rfl

-- **Exercise**
example (hP : P) : R → P → Q → (hP = hP) := by
  intro _ _ _
  rfl

-- **Exercise**
example (n : ℕ) (h : n = 5) : n = 2 + 3 := by
  rw [h]

-- **Exercise**
example (n m : ℕ) (hn : n = 5) (hm : 11 = m) : m = n + 6 := by
  rw [hn, ← hm]

-- **Exercise**
example (α : Type) (a b c : α) (H : (a = b) → P ) (h1 : c = a) (h2 : b = c) : P := by
  apply H
  rw [h2]
  rw [← h1]
  -- exact h2

-- **Exercise**
example : P ∧ Q → Q := by
  intro h
  exact h.2

-- **Exercise**
example : (P → Q → R) → P ∧ Q → R := by
  intro h1 h2
  apply h1
  · exact h2.1
  · exact h2.2

-- `∧` is symmetric
-- **Exercise**
example : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.right
  · exact h.1


-- `∧` is transitive
-- **Exercise**
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2
  constructor
  · exact h1.1
  · exact h2.2

-- **Exercise**
example : False → P ∧ False := by
  intro h
  exfalso
  exact h

-- **Exercise**
example : (P ∧ Q → R) → P → Q → R := by
  intro h hP hQ
  apply h
  constructor
  · exact hP
  · exact hQ

-- **Exercise**
example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ

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


-- **Exercise**
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1 h2 h3
  rcases h3 with h31 | h32
  · left
    exact h1 h31
  · right
    exact h2 h32


-- **Exercise**
example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h1 h2
  rcases h2 with h21 | h22
  · left
    exact h1 h21
  · right
    exact h22
