import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometrySecondDictionary
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointHighDensity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData

/-- The actual fixed dictionary unit and first arithmetic label force a
nonzero encoded first frequency. -/
theorem geometry_first_frequency_ne_zero {ι α Label : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (hu₀ : u₀≠0)(s : Input ι)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j) :
    jointFirstFrequency (!reflected) u₀
      (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O))
      (secondEncodedRow (fun l=>(d l).block) first r)≠0 := by
  apply actual_joint_first_frequency_ne_zero _ _ _ _ hu₀ (Units.ne_zero _)
  change Supported (first r.val.1).1.1
  rw [hfirst]
  exact (geometryFirstSource s R seed K Z ξ hK bin j.1).hC

/-- Both signs of the actual second row have a canonical natural-row
representative in the same fixed two-ray dictionary, for a parent presented by
an excluded natural row of the dictionary. All nonzero and Euler puncture gates
follow from the physical input. -/
theorem actual_geometry_natural_dictionary_presented {ι α Label : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected second : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (hu₀ : u₀≠0)(s : Input ι)(hη : ParentPresentation s.η F₀ R₀)
    (R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (hR : (d r.val.1).R≠0)(ψ : RayCharacter) :
    let unit := fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
    let hf := geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin j d first r hfirst
    let key₀ := secondEncodedNonzeroRow (fun l=>(d l).block) first r (!reflected) u₀ unit hf
    let key := if second then reflectedNonzeroJointLabel key₀ else key₀
    let z := if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let hz : z≠0 := by
      dsimp only [z]; split
      · exact neg_ne_zero.mpr ((d r.val.1).rows_ne _ r.val.2.2.2.property)
      · exact (d r.val.1).rows_ne _ r.val.2.2.2.property
    let puncture := (d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)
    let holes := (d r.val.1).input.η.modulus*puncture
    holes≠0 ∧ ∀I : Ideal O,
      idealCoeff (excluded (naturalRow ((d r.val.1).τ ψ) z hz).character puncture) I=
      idealCoeff (excluded (naturalRow (secondFixedDictionary η₀
        (geometryDictionaryRay reflected s R seed K Z ξ hK bin j,ψ))
        (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character holes) I := by
  intro unit hf key₀ key z hz puncture holes
  have hp : puncture≠0 := by
    apply mul_ne_zero hR
    dsimp only [puncture] at *
    split <;> first | exact (d r.val.1).hC.1 | exact (d r.val.1).hD.1
  refine ⟨mul_ne_zero (d r.val.1).input.η.modulus_ne_bot hp,?_⟩
  intro I
  let G := naturalRow (childCharacter η₀ (geometryDictionaryRay reflected s R seed K Z ξ hK bin j))
    (jointFirstFrequency (!reflected) u₀ unit (secondEncodedRow (fun l=>(d l).block) first r)) hf
  cases second
  · exact actual_geometry_second_dictionary reflected η₀ u₀ F₀ R₀ s hη R seed K Z ξ hK bin j
      d first r hparent hfirst hf G ψ (naturalRow _ _ hz) hR I
  · exact actual_geometry_second_reflected_dictionary reflected η₀ u₀ F₀ R₀ s hη R seed K Z ξ hK bin j
      d first r hparent hfirst hf G ψ (naturalRow _ _ hz) hR I

/-- Both signs of the actual second row have a canonical natural-row
representative in the same fixed two-ray dictionary. All nonzero and Euler
puncture gates follow from the physical input. -/
theorem actual_geometry_natural_dictionary {ι α Label : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected second : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (hu₀ : u₀≠0)(s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (hR : (d r.val.1).R≠0)(ψ : RayCharacter) :
    let unit := fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
    let hf := geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin j d first r hfirst
    let key₀ := secondEncodedNonzeroRow (fun l=>(d l).block) first r (!reflected) u₀ unit hf
    let key := if second then reflectedNonzeroJointLabel key₀ else key₀
    let z := if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let hz : z≠0 := by
      dsimp only [z]; split
      · exact neg_ne_zero.mpr ((d r.val.1).rows_ne _ r.val.2.2.2.property)
      · exact (d r.val.1).rows_ne _ r.val.2.2.2.property
    let puncture := (d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)
    let holes := (d r.val.1).input.η.modulus*puncture
    holes≠0 ∧ ∀I : Ideal O,
      idealCoeff (excluded (naturalRow ((d r.val.1).τ ψ) z hz).character puncture) I=
      idealCoeff (excluded (naturalRow (secondFixedDictionary η₀
        (geometryDictionaryRay reflected s R seed K Z ξ hK bin j,ψ))
        (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character holes) I :=
  actual_geometry_natural_dictionary_presented reflected second η₀ u₀ F₀ R₀ hu₀ s (parentPresentation_of_eq hη)
    R seed K Z ξ hK bin j d first r hparent hfirst hR ψ

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
