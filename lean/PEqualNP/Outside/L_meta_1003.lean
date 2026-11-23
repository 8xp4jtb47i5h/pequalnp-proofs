import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1003

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
    HasCircuitSize n f s := by
  refine ⟨⟨gs, o⟩, ?_, h2, h3⟩
  intro g hg
  obtain ⟨h4, h5⟩ := all_ok gs h1 g hg
  refine ⟨?_, by omega⟩
  rcases h4 with h4 | h4 <;> simp [h4]

set_option maxRecDepth 100000 in
theorem c0 : (PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 13) :=
  mk _ _ _ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 17]⟩] 20 (by decide) (by decide) (by decide)

end PEqualNP.Outside.L_meta_1003

theorem PEqualNP.Outside.L_meta_1003 : PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 13 :=
  PEqualNP.Outside.L_meta_1003.c0
