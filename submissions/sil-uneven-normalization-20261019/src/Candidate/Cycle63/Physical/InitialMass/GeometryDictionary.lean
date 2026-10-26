import Candidate.Cycle63.Physical.InitialMass.FirstUniformDictionary
import Candidate.Cycle63.Physical.InitialMass.GeometryMainRadius
import Candidate.Cycle63.Physical.InitialMass.SecondEncodedGates

/- Original module: Candidate.Cycle63.Physical.InitialMass.FirstDictionaryIdentity. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
local notation "O" => HeckeFamily.O

/-- Choose the signed unit once per arithmetic label, before the first
projector, dyads or ray characters. Unsupported labels use the identity. -/
def firstDictionaryUnit (left : Bool)(η : Character)(u₀ : O)(F₀ : NaturalRow η u₀)
    (R : Ideal O)(l : FirstSourceLabel) : Oˣ :=
  if h : Supported l.1.1 then
    if left then Classical.choose (uniform_first_left_natural_parent_mask η u₀ F₀ R fixedBadMask
      l.1.1 l.1.2 h l.2.val)
    else Classical.choose (uniform_first_right_natural_parent_mask η u₀ F₀ R fixedBadMask
      l.1.1 l.1.2 h l.2.val)
  else 1

/-- Every actual left member of the fixed pair uses the same preselected
arithmetic-label unit, across all first ray choices. -/
theorem actual_fixed_pair_left_dictionary (η : Character)(u₀ : O)(F₀ : NaturalRow η u₀)
    (R : Ideal O)(l : FirstSourceLabel)(hC : Supported l.1.1)
    (ξ₁ ξ₂ : RayCharacter)(F : FixedPair (excluded F₀.character R) l.1.1 l.1.2 hC l.2.val ξ₁ ξ₂)
    (G : NaturalRow (childCharacter η (firstPhaseCharacter l.1.1 l.1.2 hC
      (activeExponent l.1.1 l.1.2)*ξ₁))
      (u₀*(firstDictionaryUnit true η u₀ F₀ R l:O)*
        primeSubsetGenerator (fun p : CommonIndex l.1.1 l.1.2=>p.val) l.2.val*
        firstSourceNumerator true l)) (I : Ideal O) :
    idealCoeff F.left I=if IsCoprime I F.left.modulus then idealCoeff G.character I else 0 := by
  have hu := Classical.choose_spec (uniform_first_left_natural_parent_mask η u₀ F₀ R fixedBadMask
    l.1.1 l.1.2 hC l.2.val)
  revert G
  unfold firstDictionaryUnit
  rw [dif_pos hC]
  simp only [↓reduceIte,firstSourceNumerator]
  intro G
  exact hu ξ₁ F.left F.left_modulus (fixed_pair_left_element F) G I

/-- The corresponding right identity retains the actual right ray and
signed numerator with a unit fixed before both ray choices. -/
theorem actual_fixed_pair_right_dictionary (η : Character)(u₀ : O)(F₀ : NaturalRow η u₀)
    (R : Ideal O)(l : FirstSourceLabel)(hC : Supported l.1.1)
    (ξ₁ ξ₂ : RayCharacter)(F : FixedPair (excluded F₀.character R) l.1.1 l.1.2 hC l.2.val ξ₁ ξ₂)
    (G : NaturalRow (childCharacter η (firstPhaseCharacter l.1.1 l.1.2 hC
      (fun p=>6-activeExponent l.1.1 l.1.2 p)*ξ₂))
      (u₀*(firstDictionaryUnit false η u₀ F₀ R l:O)*
        primeSubsetGenerator (fun p : CommonIndex l.1.1 l.1.2=>p.val) l.2.val*
        firstSourceNumerator false l)) (I : Ideal O) :
    idealCoeff F.right I=if IsCoprime I F.right.modulus then idealCoeff G.character I else 0 := by
  have hu := Classical.choose_spec (uniform_first_right_natural_parent_mask η u₀ F₀ R fixedBadMask
    l.1.1 l.1.2 hC l.2.val)
  revert G
  unfold firstDictionaryUnit
  rw [dif_pos hC]
  simp only [↓reduceIte,firstSourceNumerator]
  intro G
  exact hu ξ₂ F.right F.right_modulus (fixed_pair_right_element F) G I

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_fixed_pair_left_dictionary
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_fixed_pair_right_dictionary
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometryDictionary. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

/-- The signed phase and the actual ray of a selected first column. -/
def geometryDictionaryRay {ι : Type*} [Fintype ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) : RayCharacter :=
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  if reflected then firstPhaseCharacter src.C src.D src.hC
    (fun p=>6-activeExponent src.C src.D p)*j.2.2.2⁻¹
  else firstPhaseCharacter src.C src.D src.hC (activeExponent src.C src.D)*j.2.2.1

/-- Exact dictionary identity for the physical column character, with the
unit indexed only by its arithmetic label. The original excluded-parent
identity is retained explicitly. -/
theorem actual_geometry_column_dictionary {ι : Type*} [Fintype ι]
    (reflected : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (G : NaturalRow (childCharacter η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK key j))
      (u₀*(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀
        (geometryFirstLabel s R seed K Z ξ hK key j):O)*
        primeSubsetGenerator (fun p : CommonIndex
          (geometryFirstLabel s R seed K Z ξ hK key j).1.1
          (geometryFirstLabel s R seed K Z ξ hK key j).1.2=>p.val)
          (geometryFirstLabel s R seed K Z ξ hK key j).2.val*
        firstSourceNumerator (!reflected) (geometryFirstLabel s R seed K Z ξ hK key j)))
    (I : Ideal O) :
    let χ := geometryColumnCharacter reflected s R seed K Z ξ hK key j
    idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff G.character I else 0 := by
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  let l := geometryFirstLabel s R seed K Z ξ hK key j
  let F := fixedPair s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹
  cases reflected
  · have hu := Classical.choose_spec (uniform_first_left_natural_parent_mask η₀ u₀ F₀ R₀
      fixedBadMask src.C src.D src.hC src.inactive)
    have hm := F.left_modulus
    have hm' : F.left.modulus = (excluded F₀.character R₀).modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive*activeConductor src.C src.D} := by simpa only [hη] using hm
    have he := fixed_pair_left_element F
    simp only [hη] at he
    change idealCoeff F.left I=if IsCoprime I F.left.modulus then idealCoeff G.character I else 0
    revert G
    unfold firstDictionaryUnit
    have hc : Supported (geometryFirstLabel s R seed K Z ξ hK key j).1.1 := src.hC
    rw [dif_pos hc]
    intro G
    exact hu j.2.2.1 F.left hm' he G I
  · have hu := Classical.choose_spec (uniform_first_right_natural_parent_mask η₀ u₀ F₀ R₀
      fixedBadMask src.C src.D src.hC src.inactive)
    have hm := F.right_modulus
    have hm' : F.right.modulus = (excluded F₀.character R₀).modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive*activeConductor src.C src.D} := by simpa only [hη] using hm
    have he := fixed_pair_right_element F
    simp only [hη] at he
    change idealCoeff F.right I=if IsCoprime I F.right.modulus then idealCoeff G.character I else 0
    revert G
    unfold firstDictionaryUnit
    have hc : Supported (geometryFirstLabel s R seed K Z ξ hK key j).1.1 := src.hC
    rw [dif_pos hc]
    intro G
    exact hu j.2.2.2⁻¹ F.right hm' he G I

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_column_dictionary
end
