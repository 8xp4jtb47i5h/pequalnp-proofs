import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1331

open PEqualNP.CircuitLowerBounds

theorem fold_agree (n : ℕ) (L : List Gate) (hL : ∀ g ∈ L, ∀ u ∈ g.inputs, n ≤ u) :
    ∀ a b : List Bool, a.length = b.length → (∀ i, n ≤ i → a.getD i false = b.getD i false) →
      (L.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).length =
        (L.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b).length ∧
      ∀ i, n ≤ i → (L.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).getD i false =
        (L.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b).getD i false := by
  induction L with
  | nil => intro a b hl hv; exact ⟨hl, hv⟩
  | cons g L ih =>
    intro a b hl hv
    have hg : g.op.eval (g.inputs.map fun i => a.getD i false) =
        g.op.eval (g.inputs.map fun i => b.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro u hu
      exact hv u (hL g (List.mem_cons_self) u hu)
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hL g' (List.mem_cons_of_mem g hg'))
    · simp [hl]
    · intro i hi
      rw [hg]
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia, List.getD_append _ _ _ _ (by omega)]
        exact hv i hi
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

end PEqualNP.Outside.L_meta_1331

theorem PEqualNP.Outside.L_meta_1331 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (G : Finset (Fin gates.length)), (∀ j : Fin gates.length, j ∉ G → ∀ u ∈ (gates.get j).inputs, n ≤ u) → ∀ k ∈ G, (∀ i ∈ G, k ≤ i) → ∀ w ∈ (gates.get k).inputs, n ≤ w → ∀ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn y) := by
  intro n gates G hG k hk hmin w hw hwn x y
  have hL : ∀ g ∈ gates.take k.val, ∀ u ∈ g.inputs, n ≤ u := by
    intro g hg u hu
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hjk : j < k.val := by
      have := hj
      simp only [List.length_take] at this
      omega
    have hjl : j < gates.length := by omega
    have hnot : (⟨j, hjl⟩ : Fin gates.length) ∉ G := by
      intro hjG
      have := hmin _ hjG
      have : k.val ≤ j := this
      omega
    have := hG ⟨j, hjl⟩ hnot u
    rw [List.getElem_take] at hu
    exact this hu
  have h := PEqualNP.Outside.L_meta_1331.fold_agree n (gates.take k.val) hL (List.ofFn x) (List.ofFn y)
    (by simp) (by
      intro i hi
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
  exact h.2 w hwn
