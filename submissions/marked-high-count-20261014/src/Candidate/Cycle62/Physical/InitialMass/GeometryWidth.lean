import Candidate.Cycle62.Physical.InitialMass.GeometryDictionary
import Candidate.Cycle62.Physical.InitialMass.SecondOrientedWidth

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput
open CenteredMomentSecondHeightFamily CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondRadicalBudget RayFourExpansion Cycle62FinalNatural
local notation "O" => HeckeFamily.O

/-- Both geometric columns retain the exact fixed-pair modulus. -/
theorem actual_geometry_column_modulus {ι : Type*} [Fintype ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)) :
    let src := geometryFirstSource s R seed K Z ξ hK bin j.1
    (geometryColumnCharacter reflected s R seed K Z ξ hK bin j).modulus=
      s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive*
          activeConductor src.C src.D} := by
  let src := geometryFirstSource s R seed K Z ξ hK bin j.1
  let F := fixedPair s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹
  cases reflected
  · exact F.left_modulus
  · exact F.right_modulus

/-- Actual selected geometry gives the retained-state width in both
orientations, including the six-amplifier gain. Its only identifications
are the second datum's literal parent character and declared cutoff. -/
theorem actual_geometry_second_width {ι α Label : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ a reserve b : ℝ)(N : ℕ)
    (hK : 0<K)(hZ : 1<Z)(hb : 0<b)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→SecondInputDatum α)(r : secondLiveRows (fun l=>(d l).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hradius : (d r.val.1).radius=frequencyRadius
      (firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
        (geometryFirstLabel s R seed K Z ξ hK bin j)) Z ξ)
    (Bmask : ℝ)(χ : RayCharacter)(Q P : Ideal O)(hP : P≠0)(hPN : (P.absNorm:ℝ)≤Z^Bmask) :
    let src := geometryFirstSource s R seed K Z ξ hK bin j.1
    let c := Real.logb Z ((if reflected then src.D else src.C).absNorm:ℝ)
    let e := Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ)
    let v := d r.val.1
    (retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive).width≤
      (Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)-max (c-e) 0-6*a-
        frequencyLoss Z 32 ξ-reserve-Real.logb Z (normValue (commonFrequencyGenerator v.C v.D))+
        Real.logb Z ((∏p∈v.inactive,p.val).absNorm:ℝ))+
      (Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2+
        Real.logb Z (4*(fixedFactor:ℝ))) := by
  let src := geometryFirstSource s R seed K Z ξ hK bin j.1
  have hmod := actual_geometry_column_modulus reflected s R seed K Z ξ hK bin j
  have hm : (d r.val.1).input.η.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive*
        activeConductor src.C src.D} := by rw [hparent]; exact hmod
  exact actual_second_live_main_width_oriented reflected d r s.η src.C src.D src.hC src.hD
    src.sameSupport src.inactive K (volume s) Z a (frequencyLoss Z 32 ξ) reserve ξ b N
    hK (volume_pos s) hZ hb hm Bmask χ Q P hP hPN hradius

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_column_modulus
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_second_width
