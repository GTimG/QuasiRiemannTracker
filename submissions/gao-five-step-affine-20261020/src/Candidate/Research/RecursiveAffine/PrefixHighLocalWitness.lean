/- The HIGH witness of a second-stage row of the second step: the row's natural state, at the label of the row at the
child multiplier, has as masked row character a masked natural row of the four-ray dictionary. Released under
Apache 2.0. -/
import Candidate.Research.RecursiveAffine.LocalGeometryWitness
import Candidate.Research.RecursiveAffine.PrefixHighPresentation
import Candidate.Cycle63.Moment.DepthTwoHighCountRows

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle153HighProvider
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic Cycle63InitialMass
open Cycle153LocalHighWitness
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource CenteredMomentEnergyState
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondExceptionalFamily IdealMobiusDivisorSum
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Excluding the unit ideal from a character keeps its modulus. -/
theorem excluded_one_modulus (σ : Character) : (excluded σ 1).modulus = σ.modulus := by
  have hsupport : CompletedGauss.primeSupport (1 : Ideal O) = ∅ := by
    change UniqueFactorizationMonoid.primeFactors (1 : Ideal O) = ∅
    exact UniqueFactorizationMonoid.primeFactors_one
  change σ.modulus*∏ P ∈ CompletedGauss.primeSupport (1 : Ideal O), P = σ.modulus
  rw [hsupport, Finset.prod_empty, mul_one]

/-- Excluding the unit ideal from a character that vanishes at zero keeps its coefficients. -/
theorem excluded_one_element (σ : Character) (hσ0 : elementCoeff σ 0 = 0) (n : O) :
    elementCoeff (excluded σ 1) n = elementCoeff σ n := by
  rw [excluded_element σ hσ0 1 one_ne_zero n, ite_eq_left isCoprime_one_right]

namespace PrefixHighPresentation
variable {Base : Type} {base : Base → Character} {η : Character} {R : Ideal O}
    (P : PrefixHighPresentation base η R)

def unit (left : Bool) : FirstSourceLabel → O :=
  fun l => (firstDictionaryUnit left η 1 P.selfRow 1 l : O)

theorem self_parent_presentation : ParentPresentation η P.selfRow 1 := by
  have hη0 : elementCoeff η 0 = 0 := by
    by_contra h
    have hs := P.supported 0 h
    exact hs.1 (by rw [Ideal.span_singleton_zero, Ideal.zero_eq_bot])
  refine ⟨?_,?_⟩
  · change η.modulus = (excluded η 1).modulus
    exact (excluded_one_modulus η).symm
  · intro z
    change elementCoeff η z = elementCoeff (excluded η 1) z
    exact (excluded_one_element η hη0 z).symm
end PrefixHighPresentation

def prefixHighLocalWitness {ι α Label : Type} [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    {Base : Type} {base : Base → Character} (η₀ : Character)
    {s : Input ι} {P₁ : Ideal O} (P : PrefixHighPresentation base s.η P₁)
    (reflected second : Bool)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0 < K) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label → SecondInputDatum α) (first : Label → FirstSourceLabel)
    (r : secondLiveRows (fun l => (d l).block))
    (hparent : (d r.val.1).input.η = geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hfirst : first r.val.1 = geometryFirstLabel s R seed K Z ξ hK bin j)
    (hR : (d r.val.1).R ≠ 0) (hPR : P₁ ∣ (d r.val.1).R) (ψ : RayCharacter)
    {Zs Bmask bΦ : ℝ} (st : NaturalState Zs Bmask bΦ) (hQM : st.fixedModulus ≤ M)
    (hQη : st.fixedModulus ≤ η₀.modulus) (zr : O) (hzr : st.radial.keep zr)
    (hchar : st.character = (d r.val.1).τ ψ)
    (hpuncture : st.puncture = (d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C))
    (hrow : zr = if second then -r.val.2.2.2.val else r.val.2.2.2.val)
:
     DepthTwoHighWitness M (extendFixedDictionary base) η₀ (nonzeroJointSourceRow
      (multiplierLabel (!reflected)
        (fun l => (firstDictionaryUnit (!reflected) s.η 1
          P.selfRow 1 l : O)) P.hv
        (if second then reflectedNonzeroJointLabel
          (secondEncodedNonzeroRow (fun l => (d l).block) first r (!reflected) 1
            (fun l => (firstDictionaryUnit (!reflected) s.η 1
              P.selfRow 1 l : O))
            (geometry_first_frequency_ne_zero reflected s.η 1
              P.selfRow 1 one_ne_zero
              s R seed K Z ξ hK bin j d first r hfirst))
        else secondEncodedNonzeroRow (fun l => (d l).block) first r (!reflected) 1
            (fun l => (firstDictionaryUnit (!reflected) s.η 1
              P.selfRow 1 l : O))
            (geometry_first_frequency_ne_zero reflected s.η 1
              P.selfRow 1 one_ne_zero
              s R seed K Z ξ hK bin j d first r hfirst)))) := by
  let hparentSelf : ParentPresentation s.η P.selfRow 1 := P.self_parent_presentation
  let W := localGeometryWitness M s.η η₀ P.selfRow reflected second s hparentSelf
    R seed K Z ξ hK bin j d first r hparent hfirst hR ψ st hQM hQη zr hzr hchar hpuncture hrow
  have hPW : P₁ ∣ W.holes := by
    change P₁ ∣ (d r.val.1).input.η.modulus *
      ((d r.val.1).R * (if second then (d r.val.1).D else (d r.val.1).C))
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hPR _) _
  let unit := P.unit (!reflected)
  let hf := geometry_first_frequency_ne_zero reflected s.η 1 P.selfRow 1 one_ne_zero
    s R seed K Z ξ hK bin j d first r hfirst
  let key₀ := secondEncodedNonzeroRow (fun l => (d l).block) first r (!reflected) 1 unit hf
  let key := if second then reflectedNonzeroJointLabel key₀ else key₀
  exact P.masked.liftLabelHighWitness M key W hPW

#print axioms prefixHighLocalWitness
end
end OAI.SevenEighths.Cycle153HighProvider
