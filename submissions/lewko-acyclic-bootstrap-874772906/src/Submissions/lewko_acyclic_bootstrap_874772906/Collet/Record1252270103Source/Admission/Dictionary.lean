/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual joint retained dictionary, including extra Newton punctures,
transports moving rows and the full initialKeep to one fixed anchor. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.Height
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.NaturalMask
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge CenteredMomentLattice
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion CenteredMomentRetainedEnergy
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily CenteredMomentTwist
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentChildRows CanonicalQuadraticSieve Cycle61Moment RayFourExpansion
open Record12518109Raw CenteredMomentSecondExceptionalFamily ActualEisensteinCubic
local notation "O" => HeckeFamily.O

/-- Equality of the literal masked ideal coefficients transports the normalized
positive row, including every natural zero. No norm contraction is used. -/
theorem positive_row_norm_dictionary {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ η : Character} {z w : O} (F : NaturalRow τ z) (G : NaturalRow η w)
    (P R : Ideal O) (hP : P≠0) (he : ∀I : Ideal O,
      idealCoeff (excluded F.character P) I=idealCoeff (excluded G.character R) I)
    (W₁ W₂ : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (scale : ι→ℝ)
    (hscale : ∀i,0<scale i) (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    ‖positiveSlotRow τ (fixedBadMask*idealGenerator P) 1 z W₁ W₂ pool β scale t X₁ X₂‖=
      ‖polynomial (excluded G.character R) false
          (normPowerProfile W₁ a b ha hs₁ hW₁ t) X₁ 0 0*
        polynomial (excluded G.character R) false
          (normPowerProfile W₂ a b ha hs₂ hW₂ t) X₂ 0 0*
        ∏i,naturalSlot (excluded G.character R) (pool i) (heightCoefficient (β i) t) (scale i)‖ := by
  have hp (W : ℝ→ℂ) (X : ℝ) :
      polynomial (excluded F.character P) false W X 0 0=
        polynomial (excluded G.character R) false W X 0 0 := by
    unfold polynomial summand coefficient
    simp only [Bool.false_eq_true,ite_false,he]
  have hs (i : ι) : naturalSlot (excluded F.character P) (pool i) (heightCoefficient (β i) t) (scale i)=
      naturalSlot (excluded G.character R) (pool i) (heightCoefficient (β i) t) (scale i) := by
    simp only [naturalSlot,he]
  rw [original_positive_normalized F P hP W₁ W₂ a b a b ha ha hs₁ hs₂ hW₁ hW₂
    pool β scale hscale t X₁ X₂ hX₁ hX₂]
  simp only [norm_mul,positive_height_phase_norm X₁ t hX₁,
    positive_height_phase_norm X₂ t hX₂,one_mul,hp,hs]

/-- This is the actual two-stage character dictionary. `hmask` is the literal
allocation mask identity; an extra divisor is part of the common factor R.
There is no assumption about the energy or about an unmodified coefficient. -/
theorem actual_joint_extra_mask
    (left second : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (l : NonzeroJointSourceLabel left u₀ unit)
    (η χ₁ : Character) (first : NaturalRow η (jointFirstFrequency left u₀ unit l.val))
    (hfirst : ∀I : Ideal O,idealCoeff χ₁ I=
      if IsCoprime I χ₁.modulus then idealCoeff first.character I else 0)
    (hC₁ : Supported l.val.1.1.1) (hD₁ : Supported l.val.1.1.2)
    (hs₁ : CompletedGauss.primeSupport l.val.1.1.1=CompletedGauss.primeSupport l.val.1.1.2)
    (hC₂ : Supported l.val.2.1.1) (hD₂ : Supported l.val.2.1.2)
    (hs₂ : CompletedGauss.primeSupport l.val.2.1.1=CompletedGauss.primeSupport l.val.2.1.2)
    (τ : RayCharacter→Character)
    (hf : Family χ₁ l.val.2.1.1 l.val.2.1.2 hC₂ hD₂ l.val.2.2.val.1 τ)
    (ξ : RayCharacter) (F : NaturalRow (τ ξ) l.val.2.2.val.2)
    (P R : Ideal O) (hP : P≠0) (hR : R≠0) (hCP : l.val.2.1.1∣P)
    (hmask : χ₁.modulus*P=R*(Ideal.span {
      primeSubsetGenerator (fun p : CommonIndex l.val.1.1.1 l.val.1.1.2=>p.val) l.val.1.2.val*
        activeConductor l.val.1.1.1 l.val.1.1.2}*
      ((if left then l.val.1.1.1 else l.val.1.1.2)*
        (if second then l.val.2.1.2 else l.val.2.1.1)))) (I : Ideal O) :
    idealCoeff (excluded F.character P) I=
      idealCoeff (excluded (naturalRow (childCharacter η ξ)
        (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
        (R*firstSourceMissing left l.val.1)) I := by
  rw [actual_joint_retained_dictionary_mask left u₀ unit l η χ₁ first hfirst
    hC₂ hD₂ hs₂ τ hf ξ F P hP hCP I,hmask]
  exact actual_joint_common_mask left second u₀ unit l hC₁ hD₁ hs₁ hC₂ hD₂ hs₂
    (childCharacter η ξ) (naturalRow _ _ (nonzeroJointSourceRow l).property) R hR I

/-- The complete ordinary/exceptional filter follows the same coefficient
identity; moving masks never create a new fixed-character source invocation. -/
theorem initialKeep_dictionary {τ η : Character} {z w : O}
    (F : NaturalRow τ z) (G : NaturalRow η w) (hz : z≠0) (hw : w≠0)
    (P R : Ideal O) (hP : P≠0) (hR : R≠0)
    (he : ∀I : Ideal O,idealCoeff (excluded F.character P) I=
      idealCoeff (excluded G.character R) I) (Q : Ideal O) :
    CenteredMomentDetectorEnergyInitialState.initialKeep η Q w ↔
      z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow τ Q fixedBadMask 1 z := by
  exact natural_initialKeep_of_masked_ideal_eq G F hw hz R P hR hP (fun I=>(he I).symm) Q

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.positive_row_norm_dictionary
#print axioms QRH.Record1252270103Source.Admission.actual_joint_extra_mask
#print axioms QRH.Record1252270103Source.Admission.initialKeep_dictionary
