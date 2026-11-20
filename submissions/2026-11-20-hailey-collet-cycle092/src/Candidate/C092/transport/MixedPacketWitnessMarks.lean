/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual complete whole-slot products, selected on the same physical fiber. -/
import Candidate.C092.transport.MixedPacketWitnessOrdinary

set_option autoImplicit false
namespace QRH.Cycle092.MixedPacketWitness
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O

/-- The whole-slot lower factor is selected from the actual native bins,
with one fixed selected set for every row in this physical fiber. -/
theorem original_whole_slot_selection {M : Ideal O} {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type} {U a ε cutoff T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε cutoff T allowance i)
    (hU : 1 < U) (ha : 1/2 ≤ a) (z : ℝ) (hz : 0 ≤ z)
    (hzL : z ≤ ∑s∈F.slots,F.widths s) :
    ∃ selected : Finset Slot,selected⊆F.slots ∧
      (∑s∈selected,F.widths s) ≤ z ∧
      ∀u∈F.rows,U^(F.q*z-(2*a-1)*F.mesh/2) ≤ ‖F.physicalProduct selected u‖ := by
  obtain ⟨selected,hsub,hpos,hlen,hspike⟩ := select_physical_product M H
    F.rows F.nonempty F.slots (fun u : FreeRow=>u.val)
    F.profile F.upper F.widths F.bin F.external U (2*a-1) F.mesh F.binWidth z
    hU (by linarith) F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<7/37) F.supply) hz hzL F.fixed_bin
  refine ⟨selected,hsub,hlen,?_⟩
  intro u hu
  apply (pow_le_pow_iff_left₀
    (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (norm_nonneg _) (by norm_num : (2:ℕ)≠0)).mp
  have hp : (U^(F.q*z-(2*a-1)*F.mesh/2))^2 =
      U^(2*F.q*z-(2*a-1)*F.mesh) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (zero_lt_one.trans hU).le]
    congr 1
    ring
  rw [hp]
  exact hspike u hu

#print axioms original_whole_slot_selection
end
end QRH.Cycle092.MixedPacketWitness
