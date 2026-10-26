import Candidate.Cycle63.Physical.InitialMass.SecondActualSources
import Candidate.Cycle63.Moment.FixedPairMasks
import Candidate.Cycle63.Moment.ReflectedJointRow
import Candidate.Cycle63.Physical.InitialMass.GeometryDictionary
import Candidate.Cycle63.Moment.ActualRowDensity

/- Original module: Candidate.Cycle63.Physical.InitialMass.SecondDictionary. -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentNaturalRowSource CenteredMomentChildRows RayFourExpansion
local notation "O" => HeckeFamily.O
/-- Equal prime supports give identical Euler masks, even when the two
common ideals have different valuations. -/
theorem excluded_common_pair_ideal (χ : Character) (R C D : Ideal O)
    (hR : R≠0) (hC : C≠0) (hD : D≠0)
    (hs : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (I : Ideal O) :
    idealCoeff (excluded χ (R*C)) I=idealCoeff (excluded χ (R*D)) I := by
  by_cases hI : I=0
  · simp only [hI,idealCoeff_zero]
  · rw [excluded_ideal _ _ (mul_ne_zero hR hC),excluded_ideal _ _ (mul_ne_zero hR hD)]
    have hc : IsCoprime I C ↔ IsCoprime I D := by
      simpa only [isCoprime_comm] using
        CenteredMomentSecondSectorColumns.coprime_of_same_support C D I hC hD hI hs
    simp only [IsCoprime.mul_right_iff,hc]

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- Exact natural-row dictionary identity for the literal second input,
with its actual puncture. Character-family and common-divisor hypotheses
are supplied by the input construction. -/
theorem actual_second_input_dictionary_mask
    (d : Label→SecondInputDatum α) (first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (hf : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)≠0)
    (η : Character)
    (F₁ : NaturalRow η (jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)))
    (hfirst : ∀I : Ideal O,idealCoeff (d r.val.1).input.η I=
      if IsCoprime I (d r.val.1).input.η.modulus then idealCoeff F₁.character I else 0)
    (ξ : RayCharacter) (F₂ : NaturalRow ((d r.val.1).τ ξ) r.val.2.2.2.val)
    (hR : (d r.val.1).R≠0) (I : Ideal O) :
    let l := secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf
    idealCoeff (excluded F₂.character ((d r.val.1).R*(d r.val.1).C)) I=
      idealCoeff (excluded (naturalRow (childCharacter η ξ)
        (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
          ((d r.val.1).input.η.modulus*((d r.val.1).R*(d r.val.1).C))) I := by
  exact actual_joint_retained_dictionary_mask left u₀ unit
    (secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf)
    η (d r.val.1).input.η F₁ hfirst (d r.val.1).hC (d r.val.1).hD
    (d r.val.1).sameSupport (d r.val.1).τ (d r.val.1).family ξ F₂ _
    (mul_ne_zero hR (d r.val.1).hC.1) (dvd_mul_left _ _) I

/-- The right column uses the negated physical row. Its canonical
partition and nonzero proof are transported by the proved reflection. -/
theorem actual_second_reflected_input_dictionary_mask
    (d : Label→SecondInputDatum α) (first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (hf : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)≠0)
    (η : Character)
    (F₁ : NaturalRow η (jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)))
    (hfirst : ∀I : Ideal O,idealCoeff (d r.val.1).input.η I=
      if IsCoprime I (d r.val.1).input.η.modulus then idealCoeff F₁.character I else 0)
    (ξ : RayCharacter) (F₂ : NaturalRow ((d r.val.1).τ ξ) (-r.val.2.2.2.val))
    (hR : (d r.val.1).R≠0) (I : Ideal O) :
    let l := reflectedNonzeroJointLabel
      (secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf)
    idealCoeff (excluded F₂.character ((d r.val.1).R*(d r.val.1).D)) I=
      idealCoeff (excluded (naturalRow (childCharacter η ξ)
        (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
          ((d r.val.1).input.η.modulus*((d r.val.1).R*(d r.val.1).D))) I := by
  have he := actual_joint_retained_dictionary_mask left u₀ unit
    (reflectedNonzeroJointLabel
      (secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf))
    η (d r.val.1).input.η F₁ hfirst (d r.val.1).hC (d r.val.1).hD
    (d r.val.1).sameSupport (d r.val.1).τ (d r.val.1).family ξ F₂ _
    (mul_ne_zero hR (d r.val.1).hC.1) (dvd_mul_left _ _) I
  apply (excluded_common_pair_ideal F₂.character (d r.val.1).R (d r.val.1).C
    (d r.val.1).D hR (d r.val.1).hC.1 (d r.val.1).hD.1 (d r.val.1).sameSupport I).symm.trans
  apply he.trans
  simpa only [mul_assoc] using excluded_common_pair_ideal _
    ((d r.val.1).input.η.modulus*(d r.val.1).R) (d r.val.1).C (d r.val.1).D
    (mul_ne_zero (d r.val.1).input.η.modulus_ne_bot hR)
    (d r.val.1).hC.1 (d r.val.1).hD.1 (d r.val.1).sameSupport I

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_input_dictionary_mask
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_reflected_input_dictionary_mask

#print axioms OAI.SevenEighths.Cycle63InitialMass.excluded_common_pair_ideal
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometrySecondDictionary. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
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
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_joint_first_mask
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_second_dictionary

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_second_reflected_dictionary
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometryNaturalDictionary. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

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

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_first_frequency_ne_zero
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_natural_dictionary
end
