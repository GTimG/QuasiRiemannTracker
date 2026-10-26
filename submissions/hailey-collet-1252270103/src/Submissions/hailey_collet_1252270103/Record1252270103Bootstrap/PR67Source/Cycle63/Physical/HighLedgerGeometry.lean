import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalCapacity.Geometry
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.FirstSourceCount
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.HighSourceEnergy
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63HighGeometry
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical CenteredMomentCommonHarmonicMass
open Cycle63Moment Cycle63FinalCapacity CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentAmplificationChildSourceCaps

def cancelledRadical (left : Bool) (C D : Ideal O) : Ideal O :=
  if left then firstLeftCancelledRadical C D else firstRightCancelledRadical C D

lemma cancelled_pos (left : Bool) (C D : Ideal O) (hC : Supported C) :
    0 < (cancelledRadical left C D).absNorm := by
  cases left <;> exact firstSubsetNorm_pos C D hC _

/-- Every common-part gate used by the high reserve follows from the actual
first canonical pair, its inactive subset, and its signed numerator. -/
theorem actual_first_gates (left : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2) (Z : ℝ) (hZ : 1<Z) :
    let c := Real.logb Z (l.1.1.absNorm:ℝ)
    let d := Real.logb Z (l.1.2.absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let R₀ := Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    0≤p ∧ 0≤E ∧ 0≤R₀ ∧ p≤ c ∧ p≤d ∧ R≤p ∧ Lc≤5*(R-R₀) := by
  dsimp only
  have hp : 0 < (commonRadical l.1.1 l.1.2).absNorm := by
    rw [first_common_radical_product]
    exact firstCommonSubsetNorm_pos _ _ hC Finset.univ
  have hp1 : (1:ℝ)≤((commonRadical l.1.1 l.1.2).absNorm:ℝ) := by exact_mod_cast hp
  have hE : (1:ℝ)≤((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ) := by
    exact_mod_cast firstCommonSubsetNorm_pos _ _ hC l.2.val
  have hR₀ : (1:ℝ)≤((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ) := by
    exact_mod_cast cancelled_pos left _ _ hC
  have hpcd := commonRadical_norm_le _ _ hC.1 hD.1
  have hpc := Real.logb_le_logb_of_le hZ (by exact_mod_cast hp) (hpcd.trans (min_le_left _ _))
  have hpd := Real.logb_le_logb_of_le hZ (by exact_mod_cast hp) (hpcd.trans (min_le_right _ _))
  have hdiv : Ideal.span {activeConductor l.1.1 l.1.2} ∣ commonRadical l.1.1 l.1.2 := by
    rw [commonRadical_active_principal]
    exact dvd_mul_right _ _
  have hr := Real.logb_le_logb_of_le hZ (active_norm_pos _ _)
    (show ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)≤
      ((commonRadical l.1.1 l.1.2).absNorm:ℝ) by
      exact_mod_cast Nat.le_of_dvd hp (map_dvd Ideal.absNorm hdiv))
  refine ⟨Real.logb_nonneg hZ hp1,Real.logb_nonneg hZ hE,
    Real.logb_nonneg hZ hR₀,hpc,hpd,hr,?_⟩
  cases left
  · exact actual_first_right_log_bound _ _ hC Z hZ
  · exact actual_first_left_log_bound _ _ hC Z hZ

/-- The density fiber's counted missing radical is exactly the inactive
complement plus the cancelled signed part, not an independent label cost. -/
theorem actual_missing_log (left : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (Z : ℝ) :
    Real.logb Z ((firstSourceMissing left l).absNorm:ℝ) =
      Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)-
      Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)+
      Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ) := by
  cases left
  · exact actual_first_right_missing_width _ _ hC _ l.2.property Z
  · exact actual_first_left_missing_width _ _ hC _ l.2.property Z

end
end OAI.SevenEighths.Cycle63HighGeometry

end Record1252270103Bootstrap.PR67
