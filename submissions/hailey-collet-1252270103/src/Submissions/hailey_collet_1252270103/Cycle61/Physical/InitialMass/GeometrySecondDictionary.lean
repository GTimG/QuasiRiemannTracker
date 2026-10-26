import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryDictionary
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondDictionary
import Submissions.hailey_collet_1252270103.Cycle61.Moment.ActualRowDensity

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

/-- The actual first-column mask in the joint-row encoding. Equality of
labels identifies the frequency without changing the fixed unit map. -/
theorem actual_geometry_joint_first_mask {ι : Type*} [Fintype ι]
    (reflected : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (l : JointSourceLabel)(hl : l.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (G : NaturalRow (childCharacter η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK bin j))
      (jointFirstFrequency (!reflected) u₀
        (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)) l)) (I : Ideal O) :
    let χ := geometryColumnCharacter reflected s R seed K Z ξ hK bin j
    idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff G.character I else 0 := by
  revert G
  unfold jointFirstFrequency
  rw [hl]
  intro G
  exact actual_geometry_column_dictionary reflected η₀ u₀ F₀ R₀ s hη R seed K Z ξ hK bin j G I

/-- Every actual second input whose parent is the selected geometric
column inherits the fixed dictionary mask. No first-mask analytic premise
is left to the second transform. -/
theorem actual_geometry_second_dictionary {ι α Label : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (hf : jointFirstFrequency (!reflected) u₀
      (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O))
      (secondEncodedRow (fun l=>(d l).block) first r)≠0)
    (G : NaturalRow (childCharacter η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK bin j))
      (jointFirstFrequency (!reflected) u₀
        (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O))
        (secondEncodedRow (fun l=>(d l).block) first r)))
    (ψ : RayCharacter)(F₂ : NaturalRow ((d r.val.1).τ ψ) r.val.2.2.2.val)
    (hR : (d r.val.1).R≠0)(I : Ideal O) :
    let unit := fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
    let key := secondEncodedNonzeroRow (fun l=>(d l).block) first r (!reflected) u₀ unit hf
    idealCoeff (excluded F₂.character ((d r.val.1).R*(d r.val.1).C)) I=
      idealCoeff (excluded (naturalRow
        (secondFixedDictionary η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK bin j,ψ))
        (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character
        ((d r.val.1).input.η.modulus*((d r.val.1).R*(d r.val.1).C))) I := by
  apply actual_second_input_dictionary_mask d first r (!reflected) u₀ _ hf _ G
  · intro J
    rw [hparent]
    exact actual_geometry_joint_first_mask reflected η₀ u₀ F₀ R₀ s hη R seed K Z ξ hK bin j
      (secondEncodedRow (fun l=>(d l).block) first r) hfirst G J
  · exact hR

/-- Every actual second input whose parent is the selected geometric
column inherits the fixed dictionary mask. No first-mask analytic premise
is left to the second transform. -/
theorem actual_geometry_second_reflected_dictionary {ι α Label : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (hf : jointFirstFrequency (!reflected) u₀
      (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O))
      (secondEncodedRow (fun l=>(d l).block) first r)≠0)
    (G : NaturalRow (childCharacter η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK bin j))
      (jointFirstFrequency (!reflected) u₀
        (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O))
        (secondEncodedRow (fun l=>(d l).block) first r)))
    (ψ : RayCharacter)(F₂ : NaturalRow ((d r.val.1).τ ψ) (-r.val.2.2.2.val))
    (hR : (d r.val.1).R≠0)(I : Ideal O) :
    let unit := fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
    let key := reflectedNonzeroJointLabel (secondEncodedNonzeroRow (fun l=>(d l).block) first r (!reflected) u₀ unit hf)
    idealCoeff (excluded F₂.character ((d r.val.1).R*(d r.val.1).D)) I=
      idealCoeff (excluded (naturalRow
        (secondFixedDictionary η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK bin j,ψ))
        (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character
        ((d r.val.1).input.η.modulus*((d r.val.1).R*(d r.val.1).D))) I := by
  apply actual_second_reflected_input_dictionary_mask d first r (!reflected) u₀ _ hf _ G
  · intro J
    rw [hparent]
    exact actual_geometry_joint_first_mask reflected η₀ u₀ F₀ R₀ s hη R seed K Z ξ hK bin j
      (secondEncodedRow (fun l=>(d l).block) first r) hfirst G J
  · exact hR

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_joint_first_mask
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_second_dictionary

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_second_reflected_dictionary
