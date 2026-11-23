import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1106 : ∀ (x : List Bool) (i k : ℕ), i < x.length → x.count true = k → ((!(x.getD i false)) = decide (k ≤ (x.eraseIdx i).count true)) := by
  intro x i k hi hk
  have hsplit : x = x.take i ++ x[i] :: x.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have herase : x.eraseIdx i = x.take i ++ x.drop (i + 1) := List.eraseIdx_eq_take_drop_succ x i
  have hget : x.getD i false = x[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have h1 := congrArg (List.count true) hsplit
  rw [List.count_append, List.count_cons] at h1
  have h2 := congrArg (List.count true) herase
  rw [List.count_append] at h2
  rw [hget, h2]
  cases h : x[i]
  · simp only [h] at h1
    simp only [Bool.not_false, beq_self_eq_true, reduceCtorEq, if_false] at h1 ⊢
    have : k ≤ List.count true (List.take i x) + List.count true (List.drop (i + 1) x) := by
      simp at h1
      omega
    simp [this]
  · simp only [h] at h1
    simp at h1
    have : ¬ k ≤ List.count true (List.take i x) + List.count true (List.drop (i + 1) x) := by
      omega
    simp [this]
