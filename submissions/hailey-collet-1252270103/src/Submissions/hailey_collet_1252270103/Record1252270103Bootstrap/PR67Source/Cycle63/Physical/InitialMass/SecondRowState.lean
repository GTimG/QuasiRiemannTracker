import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondActualSources
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalNatural.State
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedWidth
open CenteredMomentSectorLocalization CenteredMomentSupport
open Cycle63FinalNatural Cycle63Moment

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

theorem actual_second_live_correlation (s : Label→SecondBlockSource)
    (r : secondLiveRows s) :
    idealCorrelation (s r.val.1).C (s r.val.1).D (s r.val.1).hC (s r.val.1).hD
      ((s r.val.1).frequency*r.val.2.2.2.val)≠0 :=
  right_ne_zero_of_mul (Finset.mem_filter.mp r.property).2.2.2

/-- Every retained physical row supplies the character conductor cap.
Cancellation of its containing block is irrelevant to this pointwise gate. -/
theorem actual_second_live_conductor (d : Label→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block)) (χ : RayCharacter) :
    ((d r.val.1).τ χ).modulus.absNorm≤(d r.val.1).input.η.modulus.absNorm*fixedFactor*
      (∏P∈(d r.val.1).inactive,P.val).absNorm*
        (Ideal.span {nonunitFrequencyGenerator (d r.val.1).C (d r.val.1).D
          (d r.val.1).inactive}).absNorm := by
  apply (d r.val.1).rowBudget
    (nonunitFrequencyGenerator (d r.val.1).C (d r.val.1).D (d r.val.1).inactive*r.val.2.2.2.val) _ χ
  simpa only [SecondInputDatum.block,originalSecondBlock,SecondBlockSource.frequency,mul_assoc]
    using actual_second_live_correlation (fun l=>(d l).block) r

/-- Width admissibility now follows from the actual retained row and its
actual character family, without a nonzero-whole-block assumption. -/
theorem actual_second_live_state_width (d : Label→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))
    (Z Bmask : ℝ) (hZ : 1<Z) (χ : RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask) :
    let v := d r.val.1
    (retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive).width≤
      Real.logb Z v.radius+Real.logb Z (v.input.η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator v.C v.D))+
        Real.logb Z ((∏p∈v.inactive,p.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  dsimp only
  rw [retainedState_width]
  have hU : (∏p∈(d r.val.1).inactive,p.val)≠0 := Finset.prod_ne_zero_iff.mpr
    (fun p _=>(commonPrime_supported_ideal _ _ (d r.val.1).hC p).1)
  exact retained_log_budget _ _ _ _ r.val.2.2.2.val _ hU
    (actual_second_live_conductor d r χ) _ _ hZ
    (actual_second_live_retained_weight (fun l=>(d l).block) r.val r.property)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
