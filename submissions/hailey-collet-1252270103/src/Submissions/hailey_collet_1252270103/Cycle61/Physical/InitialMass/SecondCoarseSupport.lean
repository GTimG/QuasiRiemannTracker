import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondFrequencyBudget
import Submissions.hailey_collet_1252270103.Cycle61.Physical.HighLedgerGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstScale
open CenteredMomentFirstCanonicalFamily Cycle61Moment Cycle61HighGeometry
open CenteredMomentRankinRadical CenteredMomentSectorLocalization CenteredMomentCommonHarmonicMass
local notation "O" => HeckeFamily.O

/-- The counted missing radical is a divisor of the actual first common
radical, so its coarse norm never incurs an additional arbitrary parameter. -/
theorem first_missing_norm_le (left : Bool)(l : FirstSourceLabel)
    (hC : Supported l.1.1)(hD : Supported l.1.2) :
    0<(firstSourceMissing left l).absNorm ∧
      (firstSourceMissing left l).absNorm≤l.1.1.absNorm ∧
      (firstSourceMissing left l).absNorm≤l.1.2.absNorm := by
  have hp := firstCommonSubsetNorm_pos l.1.1 l.1.2 hC
    (firstMissingCommon l.1.1 l.1.2 l.2.val left)
  have hr : 0<(commonRadical l.1.1 l.1.2).absNorm := by
    rw [first_common_radical_product]
    exact firstCommonSubsetNorm_pos _ _ hC Finset.univ
  have hd : firstSourceMissing left l∣commonRadical l.1.1 l.1.2 := by
    rw [first_common_radical_product]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
  have hn := Nat.le_of_dvd hr (map_dvd Ideal.absNorm hd)
  have hb := commonRadical_norm_le l.1.1 l.1.2 hC.1 hD.1
  exact ⟨hp,hn.trans (by exact_mod_cast (le_min_iff.mp hb).1),hn.trans (by exact_mod_cast (le_min_iff.mp hb).2)⟩

/-- A polynomial bound for the actual signed first numerator follows from
its exact cancellation ledger, independently of the row or ray choices. -/
theorem first_numerator_log_le (left : Bool)(l : FirstSourceLabel)
    (hC : Supported l.1.1)(hD : Supported l.1.2)(Z : ℝ)(hZ : 1<Z) :
    Real.logb Z (normValue (firstSourceNumerator left l))≤5*Real.logb Z (l.1.1.absNorm:ℝ) := by
  obtain ⟨hp,hE,hR₀,hpc,hpd,hRp,hLc⟩ := actual_first_gates left l hC hD Z hZ
  change Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)≤_
  linarith

/-- The fixed-row support cap in the joint reconstruction theorem follows
from the actual row cap and the first common-ideal cap. -/
theorem joint_missing_support_cap (left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)
    (l : NonzeroJointSourceLabel left u₀ unit)(hC : Supported l.val.1.1.1)
    (hD : Supported l.val.1.1.2)(Z q A : ℝ)(hZ : 0<Z)
    (hrow : normValue (jointSourceRow left u₀ unit l.val)≤Z^q)
    (hfirst : (l.val.1.1.1.absNorm:ℝ)≤Z^A) :
    ((firstSourceMissing left l.val.1).absNorm:ℝ)≤Z^A ∧
      ((Ideal.span {jointSourceRow left u₀ unit l.val}*firstSourceMissing left l.val.1).absNorm:ℝ)≤Z^(q+A) := by
  have hm : ((firstSourceMissing left l.val.1).absNorm:ℝ)≤Z^A :=
    (Nat.cast_le.mpr (first_missing_norm_le left l.val.1 hC hD).2.1).trans hfirst
  refine ⟨hm,?_⟩
  rw [map_mul,Nat.cast_mul,Real.rpow_add hZ]
  exact mul_le_mul hrow hm (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.first_missing_norm_le
#print axioms OAI.SevenEighths.Cycle61InitialMass.first_numerator_log_le
#print axioms OAI.SevenEighths.Cycle61InitialMass.joint_missing_support_cap
