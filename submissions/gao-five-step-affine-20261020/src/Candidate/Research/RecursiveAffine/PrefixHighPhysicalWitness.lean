/- The HIGH witness of a second-stage row of the second step: the row's natural state, at the label of the row at the
child multiplier, has as masked row character a masked natural row of the four-ray dictionary. Released under
Apache 2.0. -/
import Candidate.Research.RecursiveAffine.PrefixHighLocalWitness
import Candidate.Cycle63.Physical.InitialMass.DepthTwoHighProducerRows
import Candidate.Cycle63.Moment.DepthTwoHighCountRows

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle153HighProvider
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily HeckeDetectorZeros LocalMoment CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic Cycle63InitialMass
open Cycle153LocalHighWitness
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource CenteredMomentEnergyState
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondExceptionalFamily IdealMobiusDivisorSum
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def prefixHighRowLabel {ι : Type} [Fintype ι] [DecidableEq ι] {Base : Type} {base : Base → Character} {η : Character} {R : Ideal O}
    (P : PrefixHighPresentation base η R) (second reflected : Bool) (s : Input ι) (seed : Ideal O)
    (Z Mrow amp μ t : ℝ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (χ₀ : RayCharacter)
    (Q : Ideal O) (m : O)
    (r : AffineHighRows reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m) :
    NonzeroJointSourceLabel (!reflected) P.mult (P.unit (!reflected)) :=
  multiplierLabel (!reflected) (P.unit (!reflected)) P.hv
    (affineHighUniversalKey η 1 P.selfRow 1 one_ne_zero second reflected s R seed Z Mrow amp μ t hZ bin
      hz₁ hz₂ χ₀ Q m r)

variable [Cycle63.AffineLedger] in
theorem prefixHighPhysicalWitness_exists {ι α Label : Type} [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
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
    (e T0 Tz : ℝ) (p : BufferIndex e) (hzb : GeometryZeroBin M H hH st η₀ hQM hQη zr hzr e T0 p)
    (hT : ((3*p.1.val : ℕ) : ℝ)*T0 ≤ Tz) :
    ∃W : DepthTwoHighWitness M (extendFixedDictionary base) η₀ (nonzeroJointSourceRow
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
              s R seed K Z ξ hK bin j d first r hfirst)))),
      bufferValue e p ≤ W.zeroMax M H hH Tz := by
  let W := prefixHighLocalWitness M η₀ P reflected second R seed K Z ξ hK bin j d first r hparent hfirst
    hR hPR ψ st hQM hQη zr hzr hchar hpuncture hrow
  refine ⟨W,?_⟩
  exact hzb.2.2.2.2.1.trans (zeroMaximum_mono _ _ hT)

#print axioms prefixHighPhysicalWitness_exists
end
end OAI.SevenEighths.Cycle153HighProvider
