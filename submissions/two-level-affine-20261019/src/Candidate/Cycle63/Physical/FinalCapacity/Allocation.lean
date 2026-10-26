import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
import Candidate.Cycle63.Physical.ClippedProjectorShell

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63FinalCapacity
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentSourceLiveColumn CenteredMomentAllocatedNaturalSource
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance allocationDecidableEq {α : Type*} : DecidableEq α := Classical.decEq _

/-- A nonzero actual frozen coefficient supplies the common divisor shift.
The error depends only on the fixed slot count and fixed support bound. -/
theorem common_reduction_log_lower (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
    (s : Input ι) (hcard : Fintype.card ι ≤ N) (hs : s.upper ≤ b)
    (C R : Ideal O) (B : actualAllocations s.pools C)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P ≠ 0)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (C.absNorm:ℝ)-(N:ℝ)*Real.logb Z b ≤
      Real.logb Z (rawReduction B.val s.P) := by
  have hr := rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hc := norm_ge_one C (allocation_ne s C B)
  have hn := (actual_reduction_norm B.val (alloc_ne s C B) C R
    (allocation_product s C B) s.ν s.W s.P s.P_pos s.lower b s.lower_pos
    (fun i x hx => ⟨(s.slot_support i hx).1,((s.slot_support i hx).2).trans hs⟩) hne).2
  rw [max_eq_right hb] at hn
  have hn' : (C.absNorm:ℝ) ≤ b^N*rawReduction B.val s.P := hn.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb hcard) hr.le)
  have hh := Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le hc) hn'
  rw [Real.logb_mul (pow_pos (zero_lt_one.trans_le hb) _).ne' hr.ne',Real.logb_pow] at hh
  linarith

/-- The first actual common child retains its exact volume dictionary even
when its character and height have changed. -/
theorem first_child_prevolume (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (χ : Character) (t : ℝ) :
    preVolume (child s C R B χ t).toData = preVolume s.toData/rawReduction B.val s.P := by
  change preVolume (commonData s C R B) = _
  exact common_preVolume s C R B

end
end OAI.SevenEighths.Cycle63FinalCapacity
