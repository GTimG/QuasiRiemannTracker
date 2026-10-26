import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.FirstUniformDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryMainRadius
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondEncodedGates

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_fixed_pair_left_dictionary
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_fixed_pair_right_dictionary
