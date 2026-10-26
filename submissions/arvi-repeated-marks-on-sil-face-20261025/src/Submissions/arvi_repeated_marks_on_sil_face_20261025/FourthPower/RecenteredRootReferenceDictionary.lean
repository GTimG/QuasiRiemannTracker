/- Copyright (c) 2026 Sil. Apache-2.0.
Original natural rows are the actual selected-ideal-one rows in the
existing reference provider. Keep and natural zeros remain literal.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RecenteredRootRows
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstReferenceEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RecenteredRootReferenceDictionary
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge ConcreteTraceCRT CompletedGauss
open CenteredMomentSecondHeightFamily CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open CenteredMomentOriginalRadialComparison CenteredMomentEnergyCapacityRemoval
open MixedPrincipalPair MixedFirstReferenceDispatch MixedFirstReferenceEnergy
open RecenteredRootRows RestoredInitialSource RestoredRootDictionary NativeInjectiveEnergy
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ:Type*} : DecidableEq κ := Classical.decEq _
variable {α:Type u}[Fintype α]{a b:ℝ}

def unitSelected (η:Character)(z:O) : Character :=
  selectedCharacterAt η fixedBadMask 1 fixedBadMask_ne_zero
    CenteredMomentAddedZero.supported_one_ideal (dvd_mul_right _ _) (dvd_mul_left _ _) z

theorem unitSelected_ideal (η:Character)(z:O)(hz:z≠0)(I:Id) :
    idealCoeff (unitSelected η z) I=idealCoeff (naturalCharacter η z) I := by
  by_cases hI:Supported I
  · let r:SelectedCharacter η fixedBadMask 1 z:=Classical.choice
      (selected_character_exists η fixedBadMask 1 z fixedBadMask_ne_zero
        CenteredMomentAddedZero.supported_one_ideal hz (dvd_mul_right _ _) (dvd_mul_left _ _))
    have hs:=r.on_supported I hI
    change idealCoeff (selectedCharacterAt η fixedBadMask 1 fixedBadMask_ne_zero
      CenteredMomentAddedZero.supported_one_ideal (dvd_mul_right _ _) (dvd_mul_left _ _) z) I=_
    rw [selectedCharacterAt,dif_pos hz]
    change idealCoeff r.character I=_
    rw [hs,naturalCharacter_eq η z hz,(naturalRow η z hz).ideal]
    simp only [primaryGenerator_one,idealRowHom_one_supported I hI,one_pow,mul_one,
      idealRowHom_argument_mul]
    ring
  · have hs:=selected_unsupported η fixedBadMask 1 fixedBadMask_ne_zero
      CenteredMomentAddedZero.supported_one_ideal (dvd_mul_right _ _) (dvd_mul_left _ _) z hz I hI
    exact hs.trans (natural_character_off_supported η z hz I hI).symm

/-- Eligibility comes from the original initialKeep, with internalQ
unchanged. No hypothesis about a newly invented character is needed. -/
theorem unitSelected_nonprincipal (η η₀:Character)(Q:Id)(z:O)
    (hk:initialKeep η (internalQ Q η₀) z) : (unitSelected η z).residue≠1 := by
  have he:¬CenteredExceptionalProfile.FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z:=
    ((initial_keep_iff η (internalQ Q η₀) z).mp hk).2
  have he':¬CenteredExceptionalProfile.FixedInducingRow η (internalQ Q η₀) fixedBadMask
      ((primaryGenerator (1:Id))^2) z := by simpa only [primaryGenerator_one,one_pow] using he
  exact selected_character_at_nonprincipal η fixedBadMask 1 fixedBadMask_ne_zero
    CenteredMomentAddedZero.supported_one_ideal (dvd_mul_right _ _) (dvd_mul_left _ _)
    z hk.1 (internalQ Q η₀) he'

theorem rectangle_character_congr (s:Source α a b)(ha:0<a)(χ ψ:Character)
    (h:∀I:Id,idealCoeff χ I=idealCoeff ψ I)(X Y:ℝ) :
    rectangle s ha χ X Y=rectangle s ha ψ X Y := by
  unfold rectangle MixedFirstPuncturedReference.rectangleRow MixedFirstPuncturedReference.tupleSum
  apply congrArg (MixedLiveNormalization.normalization (X*Y) s.P * ·)
  apply Finset.sum_congr rfl
  intro v hv
  rw [h]

theorem natural_reference_norm (s:Source α a b)(ha:0<a)(η:Character)
    (z:O)(hz:z≠0)(X Y:ℝ) :
    ‖rectangle s ha (naturalCharacter η z) X Y‖=
      ‖heightRectangle s ha (unitSelected η z) 0 X Y‖ := by
  calc
    _=‖rectangle s ha (unitSelected η z) X Y‖:=congrArg norm
      (rectangle_character_congr s ha _ _ (fun I=>(unitSelected_ideal η z hz I).symm) X Y)
    _=_:=rectangle_height_zero_norm s ha (unitSelected η z) X Y

/-- Finite original reference energy is below the EXISTING provider's
kept radial energy. The initial exclusion remains on the right. -/
theorem finite_reference_le_radial (s:Source α a b)(ha:0<a)
    (η η₀:Character)(Q:Id)(Φ:𝓢(ℝ,ℂ))(K bΦ X Y:ℝ)(hK:0<K)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Iic bΦ)(hΦ:∀x,0≤(Φ x).re)(rows:Finset O) :
    (∑z∈rows,initialWeight η η₀ Q Φ K z*‖rectangle s ha (naturalCharacter η z) X Y‖^2)≤
      radialEnergy (fun z=>heightRectangle s ha (unitSelected η z) 0 X Y)
        (initialKeep η (internalQ Q η₀)) Φ K := by
  let f:=fun z:O=>heightRectangle s ha (unitSelected η z) 0 X Y
  let g:=fun z:O=>if initialKeep η (internalQ Q η₀) z then
    ‖f z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hg:∀z,0≤g z:=by
    intro z
    dsimp only [g]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl
  have hsum:=compact_radial_summable f (initialKeep η (internalQ Q η₀)) Φ K bΦ hK hs
  have he:(∑z∈rows,initialWeight η η₀ Q Φ K z*‖rectangle s ha (naturalCharacter η z) X Y‖^2)=
      ∑z∈rows,g z := by
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hk:initialKeep η (internalQ Q η₀) z
    · simp only [initialWeight,hk,ite_true,g,natural_reference_norm s ha η z hk.1 X Y,f]
      ring
    · simp only [initialWeight,hk,ite_false,g,zero_mul]
  rw [he]
  change (∑z∈rows,g z)≤∑'z:O,g z
  exact hsum.sum_le_tsum rows (fun z _=>hg z)

end
end Candidate.FourthPower.RecenteredRootReferenceDictionary
