import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.CellGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.FirstLevel
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63FinalCapacity
noncomputable section
open scoped Classical BigOperators
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
variable {ι : Type*} [Fintype ι]

variable [Cycle63.AffineLedger] in
/-- The original affine cell, rather than an old parent-capacity gate, pays
the old 9/2 final capacity. Raw logarithms are bounded by clamped lengths. -/
theorem original_affine_capacity (s : Input ι) (Z M : ℝ) (hZ : 1 < Z) (hM : 0 < M)
    (hz : Cycle63.AffineLedger.slotFloor*M ≤ ∑ i, Real.logb Z (s.P i) ∧
      (∑ i, Real.logb Z (s.P i)) ≤ Cycle63.AffineLedger.slotTop*M)
    (haffine : length Z s.X₁+length Z s.X₂+
      Cycle63.AffineLedger.lam*(∑ i, Real.logb Z (s.P i)) ≤ Cycle63.AffineLedger.B*M) :
    let b := Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑ i,Real.logb Z (s.P i))/M))
    Real.logb Z (volume s)+(6*Cycle63.Optimization.slotPrice-1)*(∑ i,Real.logb Z (s.P i)) ≤ M+M*Cycle63.AffineLedger.g b := by
  dsimp only
  obtain ⟨_,_,hcap,_,_⟩ := Cycle63.AffineLedger.normalized_cell_bounds hM hz haffine
  have hh := (le_max_left (length Z s.X₁+length Z s.X₂+
    (6*Cycle63.Optimization.slotPrice)*(∑ i,Real.logb Z (s.P i))-M) 0).trans hcap
  rw [input_volume_log]
  linarith [raw_log_le_length Z s.X₁ hZ s.X₁_pos,
    raw_log_le_length Z s.X₂ hZ s.X₂_pos]

end
end OAI.SevenEighths.Cycle63FinalCapacity

end Record1252270103Bootstrap.PR67
