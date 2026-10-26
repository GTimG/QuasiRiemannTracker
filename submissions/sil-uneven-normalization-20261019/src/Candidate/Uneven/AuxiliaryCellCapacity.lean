/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryWidthGrid
import Candidate.Cycle63.Physical.FinalCapacity.Final
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryCapacity
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
variable {ι : Type*} [Fintype ι]

theorem original_affine_capacity (s : Input ι) (Z M : ℝ)
    (hZ : 1<Z) (hM : 0<M)
    (hz : Sil.Uneven.AuxiliarySource.widthLo*M≤∑i,Real.logb Z (s.P i) ∧
      (∑i,Real.logb Z (s.P i))≤Sil.Uneven.AuxiliarySource.widthHi*M)
    (haffine : length Z s.X₁+length Z s.X₂+
      Sil.Uneven.AuxiliarySource.lambda*(∑i,Real.logb Z (s.P i))≤Sil.Uneven.AuxiliarySource.B*M) :
    Real.logb Z (volume s)+(6*Sil.Uneven.AuxiliarySource.kappa-1)*(∑i,Real.logb Z (s.P i))≤
      M+M*Sil.Uneven.AuxiliarySource.gap (Sil.Uneven.AuxiliarySource.widthCellUpper ((∑i,Real.logb Z (s.P i))/M)) := by
  have ht : (∑i,Real.logb Z (s.P i))/M ∈ Set.Icc Sil.Uneven.AuxiliarySource.widthLo Sil.Uneven.AuxiliarySource.widthHi :=
    ⟨(le_div_iff₀ hM).mpr hz.1,(div_le_iff₀ hM).mpr hz.2⟩
  have hu := (Sil.Uneven.AuxiliarySource.widthCellUpper_bounds ht).2.1
  have hzu := (div_le_iff₀ hM).mp hu
  have hc : 0≤6*Sil.Uneven.AuxiliarySource.kappa-Sil.Uneven.AuxiliarySource.lambda := by
    norm_num [Sil.Uneven.AuxiliarySource.kappa,Sil.Uneven.AuxiliarySource.lambda]
  have hh := mul_le_mul_of_nonneg_left hzu hc
  rw [input_volume_log]
  unfold Sil.Uneven.AuxiliarySource.gap
  nlinarith [raw_log_le_length Z s.X₁ hZ s.X₁_pos,
    raw_log_le_length Z s.X₂ hZ s.X₂_pos]

end
end OAI.SevenEighths.AuxiliaryCapacity
