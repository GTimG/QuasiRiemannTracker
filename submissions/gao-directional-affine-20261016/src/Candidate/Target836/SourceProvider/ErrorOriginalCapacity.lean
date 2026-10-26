import Candidate.Target836.SourceProvider.ErrorNamed
import Candidate.Cycle63.Moment.CellGeometry
import Candidate.Cycle63.Physical.FinalCapacity.Final
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

set_option autoImplicit false
namespace Target874836.SourceProvider.ErrorCapacity
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
variable {ι : Type*} [Fintype ι]

/-- The original affine cell, rather than an old parent-capacity gate, pays
the old 9/2 final capacity. Raw logarithms are bounded by clamped lengths. -/
theorem original_affine_capacity (s : Input ι) (Z M : ℝ) (hZ : 1 < Z) (hM : 0 < M)
    (hz : (17/500)*M  ≤  ∑ i, Real.logb Z (s.P i) ∧
      (∑ i, Real.logb Z (s.P i))  ≤  (1/25)*M)
    (haffine : length Z s.X₁+length Z s.X₂+
      Named.lam*(∑ i, Real.logb Z (s.P i))  ≤  Named.B*M) :
    let b := Cycle63.Arithmetic.cellUpper
      (Cycle63.Moment.originalCell ((∑ i,Real.logb Z (s.P i))/M))
    Real.logb Z (volume s)+(7/2)*(∑ i,Real.logb Z (s.P i))  ≤  M+M*Named.errorGap b := by
  dsimp only
  have ht : 17/500  ≤  (∑i,Real.logb Z (s.P i))/M ∧ (∑i,Real.logb Z (s.P i))/M  ≤  1/25 :=
    ⟨(le_div_iff₀ hM).mpr hz.1,(div_le_iff₀ hM).mpr hz.2⟩
  have hu := (Cycle63.Moment.originalCell_mem ht).2.2.2
  have hzu := (div_le_iff₀ hM).mp hu
  have hc : 0  ≤  (9/2 : ℝ)-Named.lam := by norm_num [Named.lam]
  have hh := mul_le_mul_of_nonneg_left hzu hc
  rw [input_volume_log]
  unfold Named.errorGap
  nlinarith [raw_log_le_length Z s.X₁ hZ s.X₁_pos,raw_log_le_length Z s.X₂ hZ s.X₂_pos]
#print axioms original_affine_capacity
end
end Target874836.SourceProvider.ErrorCapacity
