import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1177

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def opOk : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

theorem opOk_spec (o : GateOp) (h : opOk o = true) : o = GateOp.and ∨ o = GateOp.or := by
  cases o <;> simp_all [opOk]

theorem all_ok (gs : List Gate)
    (h : gs.all (fun g => opOk g.op && g.inputs.length == 2) = true) :
    ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact ⟨opOk_spec _ h1.1, h1.2⟩

theorem mk (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) (gs : List Gate) (o : ℕ)
    (h1 : gs.all (fun g => opOk g.op && g.inputs.length == 2) = true) (h2 : gs.length ≤ s)
    (h3 : ∀ x : Fin n → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  refine ⟨⟨gs, o⟩, ?_, h2, h3⟩
  intro g hg
  obtain ⟨h4, h5⟩ := all_ok gs h1 g hg
  refine ⟨?_, by omega⟩
  rcases h4 with h4 | h4 <;> simp [h4]

set_option maxRecDepth 100000 in
theorem c0 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 7)) x) :=
  mk _ _ _ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 14]⟩] 16 (by decide) (by decide) (by decide)

end PEqualNP.Outside.L_meta_1177

theorem PEqualNP.Outside.L_meta_1177 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 7)) x :=
  PEqualNP.Outside.L_meta_1177.c0
