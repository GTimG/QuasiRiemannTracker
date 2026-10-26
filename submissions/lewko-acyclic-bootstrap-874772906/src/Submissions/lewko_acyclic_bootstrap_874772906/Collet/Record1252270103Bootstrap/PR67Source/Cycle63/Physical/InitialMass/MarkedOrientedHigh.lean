import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.HighLedgerGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.MarkedHighLedger
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.NonexceptionalLedger
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalCapacity.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonHarmonicMass
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.FirstNumeratorValuation
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.ValuationLabels
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical CenteredMomentCommonHarmonicMass
open Cycle63Moment Cycle63FinalCapacity CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentAmplificationChildSourceCaps

open Cycle63HighGeometry

/-- The balanced HIGH saving of an actual label in its physical orientation, with the parent's reserve
`M (1 - ρ) - δ A - a (5 - 6ρ)` kept: with its surplus kept, the common part is paid at the rate of the valuation cone in
the bin. -/
theorem actual_high_joint_allocation_saving_oriented_reserve (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2) (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z δ M A a : ℝ)
    (hZ : 1 < Z) (hδ : Cycle63.Arithmetic.q0 ≤ δ ∧ δ ≤ 3/4) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let R₀ := Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let g₂ := Real.logb Z (normValue (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂))
    let t₂ := Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)
    M*(ρ-1)+δ*A+a*(5-6*ρ)+(1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
      max (3*c-5*d-R) 0/6+ρ*Lc+R₀+g₂-t₂-(1+δ)*b₂-ValuationCone.surplus c d p R ≤
        -(M*(1-ρ)-δ*A-a*(5-6*ρ))-ValuationCone.commonRate δ*(c+b₂) := by
  dsimp only
  obtain ⟨hρlo,hρhi,_⟩ := Cycle63.Physical.high_density_bounds hδ
  have hcommon := ValuationCone.actual_first_common_saving reflected l hC hD heq Z
    (LocalMoment.unmarkedDensity δ) δ hZ (by linarith) (by linarith [Cycle63.Arithmetic.rho0_bounds.2])
  dsimp only at hcommon
  unfold ValuationCone.firstCommon at hcommon
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
  have hγ : ValuationCone.commonRate δ≤δ := by
    unfold ValuationCone.commonRate
    linarith [le_max_left (3/19:ℝ) (4*LocalMoment.unmarkedDensity δ-5/4)]
  obtain ⟨_,hE,_⟩ := actual_first_gates (!reflected) l hC hD Z hZ
  change _≤-ValuationCone.commonRate δ*_-_ at hcommon
  have hh := Cycle63.Physical.high_joint_allocation_saving_reserve (M := M) (A := A) (a := a)
    (p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)) hE le_rfl hb₂ hg₂ hγ
    hcommon (actual_unit_log_nonneg C₂ D₂ hC₂ U Z hZ)
  unfold Cycle63.Physical.highJointExcess at hh
  linarith only [hh]

/-- The balanced HIGH saving of an actual label in its physical orientation: with its surplus kept,
the common part is paid at the rate of the valuation cone in the bin. -/
theorem actual_high_joint_allocation_saving_oriented (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2) (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a : ℝ)
    (hZ : 1<Z) (_hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4) (_hM : 0≤M)
    (hA : A≤M*Cycle63.Arithmetic.totalA b)
    (ha : a≤M*Cycle63.Arithmetic.amp b) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let R₀ := Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let g₂ := Real.logb Z (normValue (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂))
    let t₂ := Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)
    M*(ρ-1)+δ*A+a*(5-6*ρ)+(1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
      max (3*c-5*d-R) 0/6+ρ*Lc+R₀+g₂-t₂-(1+δ)*b₂-ValuationCone.surplus c d p R ≤
        -M*Cycle63.Physical.highMainReserve b δ-ValuationCone.commonRate δ*(c+b₂) := by
  have hh := actual_high_joint_allocation_saving_oriented_reserve reflected second l hC hD heq
    C₂ D₂ hC₂ hD₂ heq₂ U Z δ M A a hZ hδ
  have hr := Cycle63.Physical.highMainReserve_le_reserve hδ hA ha
  dsimp only at hh ⊢
  linarith only [hh, hr]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
