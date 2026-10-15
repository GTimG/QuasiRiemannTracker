import Candidate.Cycle62.Moment.CellGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62FinalCapacity
noncomputable section
open scoped Classical BigOperators
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
variable {ι : Type*} [Fintype ι]

/-- The original affine cell, rather than an old parent-capacity gate, pays
the old 9/2 final capacity. Raw logarithms are bounded by clamped lengths. -/
theorem original_affine_capacity (s : Input ι) (Z M : ℝ) (hZ : 1 < Z) (hM : 0 < M)
    (hz : (17/500)*M ≤ ∑ i, Real.logb Z (s.P i) ∧
      (∑ i, Real.logb Z (s.P i)) ≤ (1/25)*M)
    (haffine : length Z s.X₁+length Z s.X₂+
      Cycle62.Arithmetic.lambda*(∑ i, Real.logb Z (s.P i)) ≤ Cycle62.Arithmetic.B*M) :
    let b := Cycle62.Arithmetic.cellUpper
      (Cycle62.Moment.originalCell ((∑ i,Real.logb Z (s.P i))/M))
    Real.logb Z (volume s)+(7/2)*(∑ i,Real.logb Z (s.P i)) ≤ M+M*Cycle62.Arithmetic.g b := by
  dsimp only
  obtain ⟨_,_,hcap,_,_⟩ := Cycle62.Moment.normalized_cell_bounds hM hz haffine
  have hh := (le_max_left (length Z s.X₁+length Z s.X₂+
    (9/2)*(∑ i,Real.logb Z (s.P i))-M) 0).trans hcap
  rw [input_volume_log]
  linarith [raw_log_le_length Z s.X₁ hZ s.X₁_pos,
    raw_log_le_length Z s.X₂ hZ s.X₂_pos]

#print axioms original_affine_capacity
end
end OAI.SevenEighths.Cycle62FinalCapacity
