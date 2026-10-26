import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.ReflectedJointRow
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointHighDensity
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondEncoding
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentNaturalRowSource CenteredMomentChildRows RayFourExpansion
/-- Equal prime supports give identical Euler masks, even when the two
common ideals have different valuations. -/
theorem excluded_common_pair_ideal (χ : Character) (R C D : Ideal O)
    (hR : R≠0) (hC : C≠0) (hD : D≠0)
    (hs : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (I : Ideal O) :
    idealCoeff (excluded χ (R*C)) I=idealCoeff (excluded χ (R*D)) I := by
  by_cases hI : I=0
  · simp only [hI,idealCoeff_zero]
  · rw [excluded_ideal _ _ (mul_ne_zero hR hC),excluded_ideal _ _ (mul_ne_zero hR hD)]
    have hc : IsCoprime I C ↔ IsCoprime I D := by
      simpa only [isCoprime_comm] using
        CenteredMomentSecondSectorColumns.coprime_of_same_support C D I hC hD hI hs
    simp only [IsCoprime.mul_right_iff,hc]

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- Exact natural-row dictionary identity for the literal second input,
with its actual puncture. Character-family and common-divisor hypotheses
are supplied by the input construction. -/
theorem actual_second_input_dictionary_mask
    (d : Label→SecondInputDatum α) (first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (hf : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)≠0)
    (η : Character)
    (F₁ : NaturalRow η (jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)))
    (hfirst : ∀I : Ideal O,idealCoeff (d r.val.1).input.η I=
      if IsCoprime I (d r.val.1).input.η.modulus then idealCoeff F₁.character I else 0)
    (ξ : RayCharacter) (F₂ : NaturalRow ((d r.val.1).τ ξ) r.val.2.2.2.val)
    (hR : (d r.val.1).R≠0) (I : Ideal O) :
    let l := secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf
    idealCoeff (excluded F₂.character ((d r.val.1).R*(d r.val.1).C)) I=
      idealCoeff (excluded (naturalRow (childCharacter η ξ)
        (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
          ((d r.val.1).input.η.modulus*((d r.val.1).R*(d r.val.1).C))) I := by
  exact actual_joint_retained_dictionary_mask left u₀ unit
    (secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf)
    η (d r.val.1).input.η F₁ hfirst (d r.val.1).hC (d r.val.1).hD
    (d r.val.1).sameSupport (d r.val.1).τ (d r.val.1).family ξ F₂ _
    (mul_ne_zero hR (d r.val.1).hC.1) (dvd_mul_left _ _) I

/-- The right column uses the negated physical row. Its canonical
partition and nonzero proof are transported by the proved reflection. -/
theorem actual_second_reflected_input_dictionary_mask
    (d : Label→SecondInputDatum α) (first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (hf : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)≠0)
    (η : Character)
    (F₁ : NaturalRow η (jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)))
    (hfirst : ∀I : Ideal O,idealCoeff (d r.val.1).input.η I=
      if IsCoprime I (d r.val.1).input.η.modulus then idealCoeff F₁.character I else 0)
    (ξ : RayCharacter) (F₂ : NaturalRow ((d r.val.1).τ ξ) (-r.val.2.2.2.val))
    (hR : (d r.val.1).R≠0) (I : Ideal O) :
    let l := reflectedNonzeroJointLabel
      (secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf)
    idealCoeff (excluded F₂.character ((d r.val.1).R*(d r.val.1).D)) I=
      idealCoeff (excluded (naturalRow (childCharacter η ξ)
        (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
          ((d r.val.1).input.η.modulus*((d r.val.1).R*(d r.val.1).D))) I := by
  have he := actual_joint_retained_dictionary_mask left u₀ unit
    (reflectedNonzeroJointLabel
      (secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf))
    η (d r.val.1).input.η F₁ hfirst (d r.val.1).hC (d r.val.1).hD
    (d r.val.1).sameSupport (d r.val.1).τ (d r.val.1).family ξ F₂ _
    (mul_ne_zero hR (d r.val.1).hC.1) (dvd_mul_left _ _) I
  apply (excluded_common_pair_ideal F₂.character (d r.val.1).R (d r.val.1).C
    (d r.val.1).D hR (d r.val.1).hC.1 (d r.val.1).hD.1 (d r.val.1).sameSupport I).symm.trans
  apply he.trans
  simpa only [mul_assoc] using excluded_common_pair_ideal _
    ((d r.val.1).input.η.modulus*(d r.val.1).R) (d r.val.1).C (d r.val.1).D
    (mul_ne_zero (d r.val.1).input.η.modulus_ne_bot hR)
    (d r.val.1).hC.1 (d r.val.1).hD.1 (d r.val.1).sameSupport I

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
