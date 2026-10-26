import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.DepthTwoGeometryDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoHighCountRows
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The HIGH witness of a second-stage row of the second step: the row's natural state, at the label of the row at the
child multiplier, has as masked row character a masked natural row of the four-ray dictionary. Released under
Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource CenteredMomentEnergyState
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondExceptionalFamily IdealMobiusDivisorSum
variable (M : Ideal O) [NeZero M]

/-- The HIGH witness of a second-stage row `r` of the second step, at the label of the row at the child multiplier
`v`. The parent `s` of the second step has the second-stage character `τ₁ j₁.2` of a first-level child presented by
`χ₁`, `first₁` and the family `τ₁`; the natural state `st` of the row has the row's character, puncture and row, and
its fixed modulus lies below `M` and the modulus of `η₀`. The witness's member of the four-ray dictionary is
`(j₁, (geometryDictionaryRay, ψ))` and its holes are those of actual_depth_two_dictionary. -/
def depthTwoGeometryWitness {ι α Label : Type} [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
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
    (hR : (d r.val.1).R ≠ 0) (hPR : P₁ ∣ (d r.val.1).R) (ψ : RayCharacter)
    {Zs Bmask bΦ : ℝ} (st : NaturalState Zs Bmask bΦ) (hQM : st.fixedModulus ≤ M)
    (hQη : st.fixedModulus ≤ η₀.modulus) (zr : O) (hzr : st.radial.keep zr)
    (hchar : st.character = (d r.val.1).τ ψ)
    (hpuncture : st.puncture = (d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C))
    (hrow : zr = if second then -r.val.2.2.2.val else r.val.2.2.2.val) :
    let F₀ := selfNaturalRow (τ₁ j₁.2) (family_element_supported χ₁ C₁ D₁ hC₁ hD₁ U₁ τ₁ hf₁ j₁.2)
    let unit := fun l => (firstDictionaryUnit (!reflected) (τ₁ j₁.2) 1 F₀ 1 l : O)
    let hf := geometry_first_frequency_ne_zero reflected (τ₁ j₁.2) 1 F₀ 1 one_ne_zero s R seed K Z ξ hK bin j d
      first r hfirst
    let key₀ := secondEncodedNonzeroRow (fun l => (d l).block) first r (!reflected) 1 unit hf
    let key := if second then reflectedNonzeroJointLabel key₀ else key₀
    let ℓ := multiplierLabel (!reflected) unit hv key
    DepthTwoHighWitness M (fourFixedDictionary η₀) η₀ (nonzeroJointSourceRow ℓ) :=
  let F₀ := selfNaturalRow (τ₁ j₁.2) (family_element_supported χ₁ C₁ D₁ hC₁ hD₁ U₁ τ₁ hf₁ j₁.2)
  let unit := fun l => (firstDictionaryUnit (!reflected) (τ₁ j₁.2) 1 F₀ 1 l : O)
  let hf := geometry_first_frequency_ne_zero reflected (τ₁ j₁.2) 1 F₀ 1 one_ne_zero s R seed K Z ξ hK bin j d
    first r hfirst
  let key₀ := secondEncodedNonzeroRow (fun l => (d l).block) first r (!reflected) 1 unit hf
  let key := if second then reflectedNonzeroJointLabel key₀ else key₀
  let hd := actual_depth_two_dictionary η₀ j₁ χ₁ w₁ first₁ hfirst₁ C₁ D₁ hC₁ hD₁ hCD₁ U₁ τ₁ hf₁ hv P₁ hP₁ hcop₁
    reflected second s hs R seed K Z ξ hK bin j d first r hparent hfirst hR hPR ψ
  { scale := Zs
    maskBound := Bmask
    profileEdge := bΦ
    state := st
    fixed_le_ray := hQM
    fixed_le_base := hQη
    row := zr
    keep := hzr
    natural := naturalRow st.character zr (st.row_ne_zero zr hzr)
    index := (j₁, (geometryDictionaryRay reflected s R seed K Z ξ hK bin j, ψ))
    holes := (χ₁.modulus*(P₁*Ideal.span {fixedBadMask}))*
      ((d r.val.1).input.η.modulus*((d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)))
    holes_ne := hd.1
    mask := by
      intro I
      have transfer (χ χ' : Character) (u u' : O) (hu : u ≠ 0) (hu' : u' ≠ 0) (hc : χ = χ') (hr : u = u') :
          (naturalRow χ u hu).character = (naturalRow χ' u' hu').character := by
        subst χ'; subst u'; rfl
      have hz' : (if second then -r.val.2.2.2.val else r.val.2.2.2.val) ≠ 0 :=
        hrow ▸ st.row_ne_zero zr hzr
      rw [transfer _ _ _ _ _ hz' hchar hrow, hpuncture]
      refine (hd.2 I).trans ?_
      exact mask_at_multiplier_row _ (!reflected) _ unit (multiplierLabel (!reflected) unit hv key) _ _ I }

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
