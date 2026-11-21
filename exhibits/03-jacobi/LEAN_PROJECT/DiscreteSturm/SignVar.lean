/-
Copyright (c) 2026 Charlie Dorsey. Released under Apache 2.0 license.
-/
import Mathlib.Data.List.SignVariations

/-!
# Sign variations are invariant under reversal

Mathlib's `List.signVariations` (the zero-deleting sign-change count) is defined through
`List.destutter`, which is head-recursive. Here we prove `signVariations l.reverse = signVariations l`
from a cons formula and a snoc formula for the number of runs `(destutter (· ≠ ·) l).length`.
-/

namespace DiscreteSturm

open List

section Runs

variable {β : Type*} [DecidableEq β]

/-- The number of maximal runs of equal consecutive entries. -/
def runs (l : List β) : ℕ := (l.destutter (· ≠ ·)).length

lemma runs_nil : runs ([] : List β) = 0 := rfl

lemma runs_singleton (a : β) : runs [a] = 1 := rfl

lemma runs_cons_cons (a b : β) (l : List β) :
    runs (a :: b :: l) = runs (b :: l) + (if a ≠ b then 1 else 0) := by
  unfold runs
  rw [destutter_cons_cons, destutter_cons']
  by_cases h : a = b
  · subst h; simp
  · simp [h]

lemma runs_append_pair (t : List β) (b a : β) :
    runs (t ++ [b, a]) = runs (t ++ [b]) + (if b ≠ a then 1 else 0) := by
  induction t with
  | nil => simp [runs_cons_cons, runs_singleton]
  | cons c t ih =>
    cases t with
    | nil => simp only [cons_append, nil_append, runs_cons_cons, runs_singleton]; omega
    | cons e t =>
      simp only [cons_append] at ih ⊢
      rw [runs_cons_cons, ih, runs_cons_cons]
      omega

lemma runs_reverse : ∀ l : List β, runs l.reverse = runs l
  | [] => rfl
  | [a] => rfl
  | a :: b :: l => by
    have ih := runs_reverse (b :: l)
    rw [reverse_cons, reverse_cons, append_assoc, singleton_append, runs_append_pair,
      ← reverse_cons, ih, runs_cons_cons]
    by_cases h : a = b
    · simp [h]
    · have h' : b ≠ a := fun e => h e.symm
      simp [h, h']

end Runs

variable {α : Type*} [Zero α] [LinearOrder α]

lemma signVariations_eq_runs (l : List α) :
    l.signVariations = runs ((l.map SignType.sign).filter (· ≠ 0)) - 1 := rfl

/-- **Sign variations are invariant under reversal.** -/
theorem signVariations_reverse (l : List α) : l.reverse.signVariations = l.signVariations := by
  rw [signVariations_eq_runs, signVariations_eq_runs, map_reverse, filter_reverse, runs_reverse]

end DiscreteSturm
