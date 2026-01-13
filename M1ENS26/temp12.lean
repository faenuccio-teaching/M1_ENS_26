import Mathlib.Tactic

variable (P Q R S : Prop)




-- `⌘`


/- # Equivalence
    Use `\iff` to write `↔` -/

-- **ToDO**
example : P ↔ P := by
  constructor
  · intro hP
    exact hP
  · intro hP
    exact hP

-- **ToDO**
lemma lemma1 : (P ↔ Q) → (Q ↔ P) := by
  intro h
  -- rcases h with h1 | h2
  constructor
  · exact h.2
  · exact h.1

-- **ToDO**
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · exact lemma1 P Q
  · exact lemma1 Q P

-- **Exercise**
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  constructor
  · intro hP
    exact h2.1 (h1.1 hP)
  · intro hR
    exact h1.2 (h2.2 hR)

-- **Exercise**
example : ¬(P ↔ ¬P) := by
  intro h
  have hP := h.1
  have hneP := h.2
  apply hP
  · apply hneP
    intro h_abs
    apply hP h_abs
    exact h_abs
  · apply hneP
    intro h_abs
    apply hP h_abs
    exact h_abs

-- **Exercise**
example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1 h2
  constructor
  · intro h3
    rcases h3 with h31 | h32
    · left
      exact h1.1 h31
    · right
      exact h2.1 h32
  · intro h_imp
    cases h_imp
    · left
      apply h1.2
      assumption
    · right
      apply h2.2
      assumption


-- `⌘`


variable (α : Type*) (p q : α → Prop) -- Use `\alpha` to write `α`

/-
  # Quantifiers
  Use `\forall` and `\exists` to write `∀` and `∃`. -/

-- **ToDO**
example (h : ∀ x : α, p x) (y : α) : p y := by
  specialize h y
  exact h

-- **Exercise** (remember the `by_cases` tactic!)
example : (∀ x, p x ∨ R) ↔ (∀ x, p x) ∨ R := by
  constructor
  · intro h
    by_cases hR : R
    · right
      exact hR
    · left
      intro x
      specialize h x
      cases h
      · assumption
      · exfalso
        exact hR (by assumption)
  · intro h
    intro x
    by_cases hR : R
    · right
      exact hR
    · left
      rcases h with h1 | h2
      · specialize h1 x
        exact h1
      · exfalso
        exact hR h2


-- **Exercise**
example : (∀ x : α, p x ∧ q x) → ∀ x : α, p x := by
  intro h
  intro x
  exact (h x).left

/- **ToDO**
    - Use of the `use` tactic -/
example (x : α) (h : p x) : ∃ y, p y := by
  use x

/- **ToDO**
    - Use of the `obtain` tactic -/
example (h : ∃ x, p x ∧ q x) : ∃ x, q x := by
  obtain ⟨x, hx⟩ := h
  use x
  exact hx.2

-- **Exercise**
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := by
  obtain ⟨x, hx⟩  := h
  use x
  constructor
  · exact hx.2
  · exact hx.1


-- **Exercise**
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  · intro h
    constructor
    · intro x
      exact (h x).left
    · intro x
      exact (h x).right
  · intro h x
    constructor
    · exact h.left x
    · exact h.right x

-- **Exercise**
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h1 h2 x
  apply h1 x
  exact h2 x

-- **Exercise**
example (h : ¬ ∃ x, ¬ p x) : ∀ x, p x := by
  intro x
  by_contra h2
  have h3 : ∃ x, ¬ p x := by
    use x
  exact h h3

/- **ToDO**
    - Use of the `rintro` tactic -/
example : (∃ x : α, R) → R := by
  rintro ⟨x, hx⟩
  exact hx


-- **Exercise**
example (x : α) : R → (∃ x : α, R) := by
  intro hR
  use x

-- **Exercise**
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor
  · rintro h ⟨x, hx⟩
    apply hx
    exact h x
  · intro H x
    by_contra h_abs
    apply H
    use x

/- **ToDO**
    - Use of the `contrapose` tactic, changing `P → Q` to `¬ Q → ¬ P`.
    Its extension `contrapose!` pushes negations from the head of a quantified expression
    to its leaves. -/
example (a : α) : (∃ x, p x → R) ↔ ((∀ x, p x) → R) := by
  constructor
  · intro h1 h2
    obtain ⟨x, hx⟩ := h1
    apply hx
    exact h2 x
  · contrapose!
    intro h
    constructor
    · intro x
      exact (h x).left
    · specialize h a
      exact h.right


-- **Exercise**
example (a : α) : (∃ x, R → p x) ↔ (R → ∃ x, p x) := by
  constructor
  · rintro ⟨x, hx⟩ hR
    use x
    exact hx hR
  · contrapose!
    intro h
    constructor
    · specialize h a
      exact h.left
    · intro x
      specialize h x
      exact h.right


/- ## `by_cases` -/

-- **ToDO**
example (h1 : P → Q) (h2 : ¬ P → Q) : Q := by
  by_cases hp : P
  · apply h1
    exact hp
  · apply h2
    exact hp

-- **ToDo**
example {α : Type} (S : Set α) : ∃ f : S → S, ∀ a b, (ha : a ∈ S) → (hb : b ∈ S) → f ⟨a, ha⟩ = f ⟨b, hb⟩ := by
  by_cases hS : S = ∅
  · use (·)
    intro a b ha hb
    exfalso
    apply hS ▸ ha
  · rw [← ne_eq, ← Set.nonempty_iff_ne_empty] at hS
    obtain ⟨y, hy⟩ := hS
    use fun x ↦ ⟨y, hy⟩
    intro a b ha hb
    rfl
