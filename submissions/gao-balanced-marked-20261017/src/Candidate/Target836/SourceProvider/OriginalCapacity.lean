import Candidate.Target836.SourceProvider.CellGeometry
import Candidate.Cycle63.Physical.FinalCapacity.Final
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

set_option autoImplicit false
namespace Target874836.SourceProvider.FinalCapacity
noncomputable section
open OAI OAI.SevenEighths
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
      Named.lam*(∑ i, Real.logb Z (s.P i)) ≤ Named.B*M) :
    let b := Cycle63.Arithmetic.cellUpper
      (Cycle63.Moment.originalCell ((∑ i,Real.logb Z (s.P i))/M))
    Real.logb Z (volume s)+(6*incumbentKappa-1)*(∑ i,Real.logb Z (s.P i)) ≤ M+M*Named.gap b := by
  dsimp only
  obtain ⟨_,_,hcap,_,_⟩ := Target874836.SourceProvider.normalized_cell_bounds hM hz haffine
  have hh := (le_max_left (length Z s.X₁+length Z s.X₂+
    (6*incumbentKappa)*(∑ i,Real.logb Z (s.P i))-M) 0).trans hcap
  rw [input_volume_log]
  linarith [raw_log_le_length Z s.X₁ hZ s.X₁_pos,
    raw_log_le_length Z s.X₂ hZ s.X₂_pos]

#print axioms original_affine_capacity
end
end Target874836.SourceProvider.FinalCapacity
