import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryNaturalDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoChildAnchor
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The dictionary identity of a grandchild: when the parent of the second step has the second-stage character of a
first-level child, every second-stage row of the second step is a masked natural row of the four-ray dictionary at the
depth-two row. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondExceptionalFamily IdealMobiusDivisorSum

/-- The child multiplier times a second-level joint row at the fixed row `1` is the joint row at the multiplier. -/
theorem multiplier_mul_jointSourceRow (left : Bool) (v : O) (unit : FirstSourceLabel → O) (ℓ : JointSourceLabel) :
    v*jointSourceRow left 1 unit ℓ = jointSourceRow left v unit ℓ := by
  unfold jointSourceRow effectiveRow
  ring

/-- The modulus of a first-column character contains the fixed bad mask. -/
theorem fixedBadMask_dvd_column_modulus {ι : Type*} [Fintype ι] (reflected : Bool) (s : Input ι)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0 < K) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)) :
    Ideal.span {fixedBadMask} ∣ (geometryColumnCharacter reflected s R seed K Z ξ hK bin j).modulus := by
  cases reflected <;> simp only [geometryColumnCharacter, Bool.false_eq_true, ↓reduceIte]
  · rw [FixedPair.left_modulus]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  · rw [FixedPair.right_modulus]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _

/-- The grandchild identity. Let the parent `s` of the second step have the second-stage character `τ₁ j₁.2` of a
first-level child presented by `χ₁`, `first₁` and the family `τ₁`, with a puncture `P₁` dividing the second step's
puncture such that every ideal coprime to `P₁` is coprime to the child's first common ideal. Every second-stage row of
the second step, in either sign, has as Euler-masked row character a masked natural row of the four-ray dictionary
member at the depth-two row, the child multiplier times the second-level joint row at the fixed row `1`; the holes are
the child's holes times the second-level holes. -/
theorem actual_depth_two_dictionary {ι α Label : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (η₀ : Character) (j₁ : RayCharacter × RayCharacter) (χ₁ : Character) (w₁ : O)
    (first₁ : NaturalRow (childCharacter η₀ j₁.1) w₁)
    (hfirst₁ : ∀ I : Ideal O, idealCoeff χ₁ I =
      if IsCoprime I χ₁.modulus then idealCoeff first₁.character I else 0)
    (C₁ D₁ : Ideal O) (hC₁ : Supported C₁) (hD₁ : Supported D₁) (hCD₁ : primeSupport C₁ = primeSupport D₁)
    (U₁ : Finset (CommonIndex C₁ D₁)) (τ₁ : RayCharacter → Character) (hf₁ : Family χ₁ C₁ D₁ hC₁ hD₁ U₁ τ₁)
    (hv : w₁*(commonFrequencyGenerator C₁ D₁*nonunitFrequencyGenerator C₁ D₁ U₁) ≠ 0)
    (P₁ : Ideal O) (hP₁ : P₁ ≠ 0) (hcop₁ : ∀ J : Ideal O, IsCoprime J P₁ → IsCoprime J C₁)
    (reflected second : Bool) (s : Input ι) (hs : s.η = τ₁ j₁.2)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0 < K) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label → SecondInputDatum α) (first : Label → FirstSourceLabel)
    (r : secondLiveRows (fun l => (d l).block))
    (hparent : (d r.val.1).input.η = geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hfirst : first r.val.1 = geometryFirstLabel s R seed K Z ξ hK bin j)
    (hR : (d r.val.1).R ≠ 0) (hPR : P₁ ∣ (d r.val.1).R) (ψ : RayCharacter) :
    let F₀ := selfNaturalRow (τ₁ j₁.2) (family_element_supported χ₁ C₁ D₁ hC₁ hD₁ U₁ τ₁ hf₁ j₁.2)
    let unit := fun l => (firstDictionaryUnit (!reflected) (τ₁ j₁.2) 1 F₀ 1 l : O)
    let hf := geometry_first_frequency_ne_zero reflected (τ₁ j₁.2) 1 F₀ 1 one_ne_zero s R seed K Z ξ hK bin j d
      first r hfirst
    let key₀ := secondEncodedNonzeroRow (fun l => (d l).block) first r (!reflected) 1 unit hf
    let key := if second then reflectedNonzeroJointLabel key₀ else key₀
    let z := if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let hz : z ≠ 0 := by
      dsimp only [z]; split
      · exact neg_ne_zero.mpr ((d r.val.1).rows_ne _ r.val.2.2.2.property)
      · exact (d r.val.1).rows_ne _ r.val.2.2.2.property
    let puncture := (d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)
    let holes := (χ₁.modulus*(P₁*Ideal.span {fixedBadMask}))*((d r.val.1).input.η.modulus*puncture)
    let v := w₁*(commonFrequencyGenerator C₁ D₁*nonunitFrequencyGenerator C₁ D₁ U₁)
    let hrow := mul_ne_zero hv (nonzeroJointSourceRow key).property
    holes ≠ 0 ∧ ∀ I : Ideal O,
      idealCoeff (excluded (naturalRow ((d r.val.1).τ ψ) z hz).character puncture) I =
      idealCoeff (excluded (naturalRow (fourFixedDictionary η₀
        (j₁, (geometryDictionaryRay reflected s R seed K Z ξ hK bin j, ψ)))
        (v*(nonzeroJointSourceRow key).val) hrow).character holes) I := by
  intro F₀ unit hf key₀ key z hz puncture holes v hrow
  have hpres : ParentPresentation s.η F₀ 1 := by
    rw [hs]
    exact ⟨(excluded_one_modulus (τ₁ j₁.2)).symm,
      fun n => (excluded_one_element (τ₁ j₁.2) (family_element_zero χ₁ C₁ D₁ hC₁ hD₁ U₁ τ₁ hf₁ j₁.2) n).symm⟩
  have hd := actual_geometry_natural_dictionary_presented reflected second (τ₁ j₁.2) 1 F₀ 1 one_ne_zero s hpres
    R seed K Z ξ hK bin j d first r hparent hfirst hR ψ
  have hb : Ideal.span {fixedBadMask} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact fixedBadMask_ne_zero
  have hfbm : Ideal.span {fixedBadMask} ∣ (d r.val.1).input.η.modulus := by
    rw [hparent]
    exact fixedBadMask_dvd_column_modulus reflected s R seed K Z ξ hK bin j
  have hPQ : P₁*Ideal.span {fixedBadMask} ∣ (d r.val.1).input.η.modulus*puncture := by
    have h := mul_dvd_mul hfbm (dvd_mul_of_dvd_left hPR (if second then (d r.val.1).D else (d r.val.1).C))
    rw [mul_comm (Ideal.span {fixedBadMask}) P₁] at h
    exact h
  have ht := child_natural_row_four_dictionary η₀ j₁ (geometryDictionaryRay reflected s R seed K Z ξ hK bin j, ψ)
    χ₁ w₁ first₁ hfirst₁ C₁ D₁ hC₁ hD₁ hCD₁ U₁ τ₁ hf₁ hv P₁ hP₁ hcop₁ (nonzeroJointSourceRow key).val
    (naturalRow (secondFixedDictionary (τ₁ j₁.2) (geometryDictionaryRay reflected s R seed K Z ξ hK bin j, ψ))
      (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property)
    (naturalRow (fourFixedDictionary η₀ (j₁, (geometryDictionaryRay reflected s R seed K Z ξ hK bin j, ψ)))
      _ hrow)
    ((d r.val.1).input.η.modulus*puncture) hd.1 hPQ
  exact ⟨mul_ne_zero (mul_ne_zero χ₁.modulus_ne_bot (mul_ne_zero hP₁ hb)) hd.1, fun I => (hd.2 I).trans (ht I)⟩

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
