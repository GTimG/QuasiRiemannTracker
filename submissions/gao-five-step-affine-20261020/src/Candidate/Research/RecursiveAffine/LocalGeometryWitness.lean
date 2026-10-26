/- A genuine local native HIGH witness at an arbitrary current source.
The physical state and row are retained; only the proved dictionary
presentation is used. Apache-2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryNaturalDictionary
import Candidate.Cycle63.Moment.DepthTwoHighCount

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle153LocalHighWitness
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource CenteredMomentEnergyState
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondExceptionalFamily IdealMobiusDivisorSum Cycle63InitialMass

variable (M : Ideal O) [NeZero M]

/-- An actual supported source character is presented by its literal self
natural row at multiplier 1. This removes the presentation premise at a
recursive stage once its physical Family supplied supported coefficients. -/
theorem self_parent_presentation (η : Character) (F₀ : NaturalRow η 1)
    (hF : F₀.character = η)
    (hs : ∀ n : O, elementCoeff η n ≠ 0 → Supported (Ideal.span {n})) :
    ParentPresentation η F₀ 1 := by
  have hzero : elementCoeff η 0 = 0 := by
    by_contra hz
    have hh := hs 0 hz
    exact hh.1 (by rw [Ideal.span_singleton_zero, Ideal.zero_eq_bot])
  have hm : (excluded η 1).modulus = η.modulus := by
    have hsupport : CompletedGauss.primeSupport (1 : Ideal O) = ∅ := by
      change UniqueFactorizationMonoid.primeFactors (1 : Ideal O) = ∅
      exact UniqueFactorizationMonoid.primeFactors_one
    change η.modulus*∏ P ∈ CompletedGauss.primeSupport (1 : Ideal O), P = η.modulus
    rw [hsupport, Finset.prod_empty, mul_one]
  constructor
  · rw [hF]
    exact hm.symm
  · intro n
    rw [hF, excluded_element η hzero 1 one_ne_zero n, ite_eq_left isCoprime_one_right]

/-- Native local dictionary witness. The anchor is a natural row of the
current source at 1. No fixed-depth representation or energy estimate is
assumed. Both signs use exactly the physical natural state, kept row and
puncture supplied by the actual geometry. -/
def localGeometryWitness {ι α Label : Type}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (η η₀ : Character) (F₀ : NaturalRow η 1)
    (reflected second : Bool) (s : Input ι) (hs : ParentPresentation s.η F₀ 1)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0 < K) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label → SecondInputDatum α) (first : Label → FirstSourceLabel)
    (r : secondLiveRows (fun l => (d l).block))
    (hparent : (d r.val.1).input.η = geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hfirst : first r.val.1 = geometryFirstLabel s R seed K Z ξ hK bin j)
    (hR : (d r.val.1).R ≠ 0) (ψ : RayCharacter)
    {Zs Bmask bΦ : ℝ} (st : NaturalState Zs Bmask bΦ)
    (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (zr : O) (hzr : st.radial.keep zr)
    (hchar : st.character = (d r.val.1).τ ψ)
    (hpuncture : st.puncture = (d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C))
    (hrow : zr = if second then -r.val.2.2.2.val else r.val.2.2.2.val) :
    let unit := fun l => (firstDictionaryUnit (!reflected) η 1 F₀ 1 l : O)
    let hf := geometry_first_frequency_ne_zero reflected η 1 F₀ 1 one_ne_zero
      s R seed K Z ξ hK bin j d first r hfirst
    let key₀ := secondEncodedNonzeroRow (fun l => (d l).block) first r (!reflected) 1 unit hf
    let key := if second then reflectedNonzeroJointLabel key₀ else key₀
    DepthTwoHighWitness M (secondFixedDictionary η) η₀ (nonzeroJointSourceRow key) :=
  let unit := fun l => (firstDictionaryUnit (!reflected) η 1 F₀ 1 l : O)
  let hf := geometry_first_frequency_ne_zero reflected η 1 F₀ 1 one_ne_zero
    s R seed K Z ξ hK bin j d first r hfirst
  let key₀ := secondEncodedNonzeroRow (fun l => (d l).block) first r (!reflected) 1 unit hf
  let key := if second then reflectedNonzeroJointLabel key₀ else key₀
  let hd := actual_geometry_natural_dictionary_presented reflected second η 1 F₀ 1 one_ne_zero s hs
    R seed K Z ξ hK bin j d first r hparent hfirst hR ψ
  { scale := Zs
    maskBound := Bmask
    profileEdge := bΦ
    state := st
    fixed_le_ray := hQM
    fixed_le_base := hQη
    row := zr
    keep := hzr
    natural := naturalRow st.character zr (st.row_ne_zero zr hzr)
    index := (geometryDictionaryRay reflected s R seed K Z ξ hK bin j, ψ)
    holes := (d r.val.1).input.η.modulus *
      ((d r.val.1).R * (if second then (d r.val.1).D else (d r.val.1).C))
    holes_ne := hd.1
    mask := by
      intro I
      have transfer (χ χ' : Character) (u u' : O) (hu : u ≠ 0) (hu' : u' ≠ 0)
          (hc : χ = χ') (hr : u = u') :
          (naturalRow χ u hu).character = (naturalRow χ' u' hu').character := by
        subst χ'; subst u'; rfl
      have hz' : (if second then -r.val.2.2.2.val else r.val.2.2.2.val) ≠ 0 :=
        hrow ▸ st.row_ne_zero zr hzr
      rw [transfer _ _ _ _ _ hz' hchar hrow, hpuncture]
      exact hd.2 I }

#print axioms self_parent_presentation
#print axioms localGeometryWitness
end
end OAI.SevenEighths.Cycle153LocalHighWitness
