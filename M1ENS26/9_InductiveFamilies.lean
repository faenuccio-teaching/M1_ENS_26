import Mathlib


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
      simp only [not_not] at hd
      apply hd
      exact h

end InductiveFamilies
