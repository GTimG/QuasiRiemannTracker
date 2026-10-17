import Candidate.Target830.Source.Schedule
import Candidate.Cycle63.Physical.FinalCapacity.Final
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
variable {ι : Type*} [Fintype ι]

theorem original_affine_capacity (P : SourcePlane) (s : Input ι) (Z M : ℝ)
    (hZ : 1<Z) (hM : 0<M)
    (hz : widthLower*M≤∑i,Real.logb Z (s.P i) ∧
      (∑i,Real.logb Z (s.P i))≤widthUpper*M)
    (haffine : length Z s.X₁+length Z s.X₂+
      P.lambda*(∑i,Real.logb Z (s.P i))≤P.B*M) :
    Real.logb Z (volume s)+(6*kappa0-1)*(∑i,Real.logb Z (s.P i))≤
      M+M*P.gap (widthCellUpper ((∑i,Real.logb Z (s.P i))/M)) := by
  have ht : (∑i,Real.logb Z (s.P i))/M ∈ Set.Icc widthLower widthUpper :=
    ⟨(le_div_iff₀ hM).mpr hz.1,(div_le_iff₀ hM).mpr hz.2⟩
  have hu := (widthCellUpper_bounds ht).2.1
  have hzu := (div_le_iff₀ hM).mp hu
  have hc : 0≤6*kappa0-P.lambda := by
    have hp := (SourcePlane.parameter_bounds P).2.2.2.2.2.2.1
    linarith
  have hh := mul_le_mul_of_nonneg_left hzu hc
  rw [input_volume_log]
  unfold SourcePlane.gap
  nlinarith [raw_log_le_length Z s.X₁ hZ s.X₁_pos,
    raw_log_le_length Z s.X₂ hZ s.X₂_pos]

end
end OAI.SevenEighths.Target830.Source
#print axioms OAI.SevenEighths.Target830.Source.original_affine_capacity
