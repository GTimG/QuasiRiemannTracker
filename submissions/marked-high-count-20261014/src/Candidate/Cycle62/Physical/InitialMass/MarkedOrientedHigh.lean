import Candidate.Cycle62.Physical.HighLedgerGeometry
import Candidate.Cycle62.Physical.MarkedHighLedger
import Candidate.Cycle62.Physical.NonexceptionalLedger
import Candidate.Cycle62.Physical.FinalCapacity.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonHarmonicMass

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical CenteredMomentCommonHarmonicMass
open Cycle62Moment Cycle62FinalCapacity CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O

open Cycle62HighGeometry

theorem actual_high_joint_excess_oriented_of_reserve (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a μ : ℝ)
    (hZ : 1<Z) (hb : 3401/100000≤b ∧ b≤1/25)
    (hδ : Cycle62.Arithmetic.q0≤δ ∧ δ≤3/4) (hM : 0≤M)
    (hA : A≤M*Cycle62.Arithmetic.totalA b)
    (ha : a≤M*Cycle62.Arithmetic.amp b) (hreserve : μ≤Cycle62.Physical.highMainReserve b δ) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let R₀ := Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let g₂ := Real.logb Z (normValue (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂))
    let t₂ := Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)
    M*(ρ-1)+δ*A+a*(5-6*ρ)+(1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
      max (3*c-5*d-R) 0/6+ρ*Lc+R₀+g₂-t₂-(1+δ)*b₂ ≤
        -M*μ := by
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
  cases reflected
  · exact Cycle62.Physical.high_joint_excess_of_reserve hb hδ hM hA ha hreserve hp hE
      (div_nonneg (le_max_right _ _) (by norm_num)) hpc hpd hRp hR₀ hLc
      hb₂ (actual_unit_log_nonneg C₂ D₂ hC₂ U Z hZ) hg₂
  · exact Cycle62.Physical.high_joint_excess_of_reserve hb hδ hM hA ha hreserve hp hE
      (div_nonneg (le_max_right _ _) (by norm_num)) hpd hpc hRp hR₀ hLc
      hb₂ (actual_unit_log_nonneg C₂ D₂ hC₂ U Z hZ) hg₂


theorem actual_high_joint_allocation_saving_oriented (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a : ℝ)
    (hZ : 1<Z) (hb : 3401/100000≤b ∧ b≤1/25)
    (hδ : Cycle62.Arithmetic.q0≤δ ∧ δ≤7/10) (hM : 0≤M)
    (hA : A≤M*Cycle62.Arithmetic.totalA b)
    (ha : a≤M*Cycle62.Arithmetic.amp b) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let R₀ := Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let g₂ := Real.logb Z (normValue (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂))
    let t₂ := Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)
    M*(ρ-1)+δ*A+a*(5-6*ρ)+(1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
      max (3*c-5*d-R) 0/6+ρ*Lc+R₀+g₂-t₂-(1+δ)*b₂ ≤
        -M*Cycle62.Physical.highMainReserve b δ-(c+b₂)/20 := by
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
  cases reflected
  · exact Cycle62.Physical.high_joint_allocation_saving hb hδ hM hA ha hp hE
      (div_nonneg (le_max_right _ _) (by norm_num)) hpc hpd hRp hR₀ hLc
      hb₂ (actual_unit_log_nonneg C₂ D₂ hC₂ U Z hZ) hg₂
  · exact Cycle62.Physical.high_joint_allocation_saving hb hδ hM hA ha hp hE
      (div_nonneg (le_max_right _ _) (by norm_num)) hpd hpc hRp hR₀ hLc
      hb₂ (actual_unit_log_nonneg C₂ D₂ hC₂ U Z hZ) hg₂

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_high_joint_allocation_saving_oriented
