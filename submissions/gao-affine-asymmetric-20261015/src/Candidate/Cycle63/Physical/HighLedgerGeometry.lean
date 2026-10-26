import Candidate.Cycle63.Physical.HighFrequency
import Candidate.Cycle63.Physical.NonexceptionalLedger
import Candidate.Cycle63.Physical.FinalCapacity.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonHarmonicMass

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63HighGeometry
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical CenteredMomentCommonHarmonicMass
open Cycle63Moment Cycle63FinalCapacity CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O

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
    0≤p ∧ 0≤E ∧ 0≤R₀ ∧ p≤c ∧ p≤d ∧ R≤p ∧ Lc≤5*(R-R₀) := by
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

/-- Literal common ideals on both sides of the second canonical transform
supply all of the final common-part inequalities in the high-bin ledger. -/
theorem actual_high_joint_excess (left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a : ℝ)
    (hZ : 1<Z) (hb : 3401/100000≤b ∧ b≤1/25)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4) (hM : 0≤M)
    (hA : A≤M*Cycle63.Arithmetic.totalA b)
    (ha : a≤M*Cycle63.Arithmetic.amp b) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z (l.1.1.absNorm:ℝ)
    let d := Real.logb Z (l.1.2.absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let R₀ := Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let g₂ := Real.logb Z (normValue (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂))
    let t₂ := Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)
    M*(ρ-1)+δ*A+a*(5-6*ρ)+(1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
      max (3*c-5*d-R) 0/6+ρ*Lc+R₀+g₂-t₂-(1+δ)*b₂ ≤
        -M*((-3140426139/871234000000)) := by
  dsimp only
  obtain ⟨hp,hE,hR₀,hpc,hpd,hRp,hLc⟩ := actual_first_gates left l hC hD Z hZ
  have hb₂ : 0≤Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    cases second
    · exact norm_ge_one C₂ hC₂.1
    · exact norm_ge_one D₂ hD₂.1
  have hg₂ : Real.logb Z (normValue (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂))≤
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) := by
    apply Real.logb_le_logb_of_le hZ
      (normValue_pos _ (CenteredMomentSecondCanonicalFrequency.commonFrequencyGenerator_ne_zero C₂ D₂ hC₂))
    cases second
    · exact actual_common_norm_le C₂ D₂ hC₂ hD₂ heq₂
    · exact actual_common_norm_le_right C₂ D₂ hC₂ hD₂ heq₂
  exact Cycle63.Physical.high_joint_excess_bound hb hδ hM hA ha hp hE
    (div_nonneg (le_max_right _ _) (by norm_num)) hpc hpd hRp hR₀ hLc
    hb₂ (actual_unit_log_nonneg C₂ D₂ hC₂ U Z hZ) hg₂

end
end OAI.SevenEighths.Cycle63HighGeometry
#print axioms OAI.SevenEighths.Cycle63HighGeometry.actual_first_gates
#print axioms OAI.SevenEighths.Cycle63HighGeometry.actual_missing_log
#print axioms OAI.SevenEighths.Cycle63HighGeometry.actual_high_joint_excess
