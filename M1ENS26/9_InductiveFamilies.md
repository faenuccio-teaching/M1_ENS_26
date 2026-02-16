---
nav_exclude: true
---

### Inductive Families and Inductive Predicates

Recall the
```lean
def EvenNaturals : Set ℕ := (· % 2 = 0)
```

* For every `n`, there is a type `(EvenNaturals n) : Prop`.
* This is a *family* of types, surely a family of *inductive* types!
* But is it an inductive type *itself*?

+++ The target
When defining `inductive NiceType` one can specify where the output lives:
```lean
inductive NiceType : Type
  | Tom : NiceType
  | Jerry : NiceType
  | f : NiceType → NiceType
  | g : ℕ → NiceType → NiceType → NiceType
```

or
```
inductive NiceProp : Prop
  | Tom : NiceProp
  | Jerry : NiceProp
  | f : NiceProp → Prop
  | g : ℕ → NiceProp → NiceProp → NiceProp
```
> The default is `Type`.

#### Families
If you want a *family* of types (say, of propositions), you simply say it straight away!
```lean
inductive NiceFamily : ℕ → Prop
  | Tom : NiceFamily 0
  | Jerry : NiceFamily 1
  | F : ∀n : ℕ, NiceFamily n → NiceFamily (n + 37)
  | G (n : ℕ) : ℕ → NiceFamily n → NiceFamily (n + 1) → NiceFamily (n + 3)
```

*Inductive Predicates* are inductive families in `Prop`.

`⌘`
+++