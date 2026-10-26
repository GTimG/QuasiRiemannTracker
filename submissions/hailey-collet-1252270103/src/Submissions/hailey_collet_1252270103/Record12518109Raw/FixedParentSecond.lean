/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Raw.FixedParentDictionary

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61InitialMass
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

theorem fixed_parent_first_frequency_ne_zero {ι α Label : Type*}
    [Fintype ι][Fintype α][DecidableEq α][Fintype Label]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))(j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j) :
    jointFirstFrequency (!reflected) 1 (fun l=>(fixedParentUnit (!reflected) s.η l:O))
      (secondEncodedRow (fun l=>(d l).block) first r)≠0 := by
  apply actual_joint_first_frequency_ne_zero _ _ _ _ one_ne_zero (Units.ne_zero _)
  change Supported (first r.val.1).1.1
  rw [hfirst]
  exact (geometryFirstSource s R seed K Z ξ hK bin j.1).hC

theorem actual_fixed_parent_joint_first_mask {ι : Type*}[Fintype ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))(j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (l : JointSourceLabel)(hl : l.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (G : NaturalRow (childCharacter s.η (geometryDictionaryRay reflected s R seed K Z ξ hK bin j))
      (jointFirstFrequency (!reflected) 1 (fun l=>(fixedParentUnit (!reflected) s.η l:O)) l))
    (I : Ideal O) :
    let χ:=geometryColumnCharacter reflected s R seed K Z ξ hK bin j
    idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff G.character I else 0 := by
  revert G
  unfold jointFirstFrequency
  rw [hl]
  intro G
  exact actual_fixed_parent_column_dictionary reflected s R seed K Z ξ hK bin j G I

/-- The two actual retained second-row signs for an arbitrary fixed parent
share the same finite two-ray dictionary. The original parent and relative
slot character need not be equal. -/
theorem actual_fixed_parent_natural_dictionary {ι α Label : Type*}
    [Fintype ι][Fintype α][DecidableEq α][Fintype Label]
    (reflected second : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))(j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (hR : (d r.val.1).R≠0)(ψ : RayCharacter) :
    let unit:=fun l=>(fixedParentUnit (!reflected) s.η l:O)
    let hf:=fixed_parent_first_frequency_ne_zero reflected s R seed K Z ξ hK bin j d first r hfirst
    let key₀:=secondEncodedNonzeroRow (fun l=>(d l).block) first r (!reflected) 1 unit hf
    let key:=if second then reflectedNonzeroJointLabel key₀ else key₀
    let z:=if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let hz : z≠0 := by
      dsimp only [z]; split
      · exact neg_ne_zero.mpr ((d r.val.1).rows_ne _ r.val.2.2.2.property)
      · exact (d r.val.1).rows_ne _ r.val.2.2.2.property
    let puncture:=(d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)
    let holes:=(d r.val.1).input.η.modulus*puncture
    holes≠0 ∧ ∀I : Ideal O,
      idealCoeff (excluded (naturalRow ((d r.val.1).τ ψ) z hz).character puncture) I=
      idealCoeff (excluded (naturalRow (secondFixedDictionary s.η
        (geometryDictionaryRay reflected s R seed K Z ξ hK bin j,ψ))
        (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character holes) I := by
  intro unit hf key₀ key z hz puncture holes
  have hp : puncture≠0 := by
    apply mul_ne_zero hR
    dsimp only [puncture]
    split <;> first | exact (d r.val.1).hC.1 | exact (d r.val.1).hD.1
  refine ⟨mul_ne_zero (d r.val.1).input.η.modulus_ne_bot hp,?_⟩
  intro I
  let G:=naturalRow (childCharacter s.η (geometryDictionaryRay reflected s R seed K Z ξ hK bin j))
    (jointFirstFrequency (!reflected) 1 unit (secondEncodedRow (fun l=>(d l).block) first r)) hf
  have hmask (J : Ideal O) : idealCoeff (d r.val.1).input.η J=
      if IsCoprime J (d r.val.1).input.η.modulus then idealCoeff G.character J else 0 := by
    rw [hparent]
    exact actual_fixed_parent_joint_first_mask reflected s R seed K Z ξ hK bin j
      (secondEncodedRow (fun l=>(d l).block) first r) hfirst G J
  cases second
  · exact actual_second_input_dictionary_mask d first r (!reflected) 1 unit hf _ G hmask ψ
      (naturalRow _ _ hz) hR I
  · exact actual_second_reflected_input_dictionary_mask d first r (!reflected) 1 unit hf _ G hmask ψ
      (naturalRow _ _ hz) hR I

end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.actual_fixed_parent_joint_first_mask
#print axioms OAI.SevenEighths.Record12518109Raw.actual_fixed_parent_natural_dictionary
