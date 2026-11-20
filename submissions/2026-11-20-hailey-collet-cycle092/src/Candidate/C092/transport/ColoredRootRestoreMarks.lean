/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Bare sextic natural row and the actual compensated first-anchor marks. -/
import Candidate.C092.transport.TwistedRawBallRootProducer
import Candidate.C092.transport.OrdinaryColumn
set_option autoImplicit false
namespace QRH.Cycle092.ColoredRootRestore
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open CanonicalRowCompletion CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorPlainFiberSource
open QRH.Cycle092.TwistedRawBallRootProducer
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

theorem topPrincipal_apply (z:O⧸(⊤:Ideal O)) : (1:MulChar (O⧸(⊤:Ideal O)) ℂ) z=1 := by
  rw [Subsingleton.elim z 1]
  exact map_one _

def bareBase : Character := Character.ofResidue ⊤ top_ne_bot 1
  (by intro u;exact topPrincipal_apply _)

theorem bareBase_element (z:O) : elementCoeff bareBase z=1 := by
  exact topPrincipal_apply _

theorem bareBase_ideal (I:Id) (hI:I≠0) : idealCoeff bareBase I=1 := by
  rw [←span_idealGenerator I,idealCoeff_span bareBase (idealGenerator_ne_zero I hI)]
  exact bareBase_element _

def bareCharacter (z:O) : Character := naturalCharacter bareBase z

theorem bare_character_ideal (z:O) (hz:z≠0) (I:Id) :
    idealCoeff (bareCharacter z) I=idealRowHom (fixedBadMask^6*z) I := by
  rw [bareCharacter,naturalCharacter_eq bareBase z hz,(naturalRow bareBase z hz).ideal]
  by_cases hI:I=0
  · subst I;simp only [map_zero,mul_zero]
  · rw [bareBase_ideal I hI,one_mul]

theorem bare_compensated_naturalSlot
    (M:Id) [NeZero M] (Hr:Subgroup (O⧸M)ˣ)
    (hHr:RayOrthogonality.globalUnits M≤Hr) (base η:Character)
    (θ:RayQuotient.Characters M Hr) (z:O) (hz:z≠0)
    (pool:Finset Id) (W:Id→ℂ) (t P:ℝ) :
    naturalSlot (bareCharacter z) pool
      (heightCoefficient (fun I=>idealCoeff (relativeCharacter M Hr hHr (base.product η.inverse) θ) I*W I) t) P =
    naturalSlot (naturalCharacter η z) pool
      (heightCoefficient (fun I=>idealCoeff (relativeCharacter M Hr hHr base θ) I*W I) t) P := by
  unfold naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [bare_character_ideal z hz I,naturalCharacter_eq η z hz,(naturalRow η z hz).ideal]
  unfold heightCoefficient
  dsimp only
  rw [relative_reanchor]
  ring

theorem normalizedSlot_natural (η:Character) (z:O) (hz:z≠0)
    (pool:Finset Id) (β:Id→ℂ) (t P:ℝ) :
    CenteredMomentWholeSlotDeletion.normalizedSlot η (fixedBadMask*idealGenerator 1) 1 z pool β t P =
      naturalSlot (naturalCharacter η z) pool (heightCoefficient β t) P := by
  unfold CenteredMomentWholeSlotDeletion.normalizedSlot naturalSlot
  rw [(naturalRow η z hz).masked_slot 1 one_ne_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [excluded_one_ideal,naturalCharacter_eq η z hz]
  unfold heightCoefficient
  ring

theorem bare_compensated_original_slot
    (M:Id) [NeZero M] (Hr:Subgroup (O⧸M)ˣ)
    (hHr:RayOrthogonality.globalUnits M≤Hr) (base η:Character)
    (θ:RayQuotient.Characters M Hr) (z:O) (hz:z≠0)
    (pool:Finset Id) (W:Id→ℂ) (t P:ℝ) :
    naturalSlot (bareCharacter z) pool
      (heightCoefficient (fun I=>idealCoeff (relativeCharacter M Hr hHr (base.product η.inverse) θ) I*W I) t) P =
    CenteredMomentWholeSlotDeletion.normalizedSlot η (fixedBadMask*idealGenerator 1) 1 z pool
      (fun I=>idealCoeff (relativeCharacter M Hr hHr base θ) I*W I) t P := by
  rw [normalizedSlot_natural η z hz]
  exact bare_compensated_naturalSlot M Hr hHr base η θ z hz pool W t P

theorem bare_compensated_supported_original_slot
    (M:Id) [NeZero M] (Hr:Subgroup (O⧸M)ˣ)
    (hHr:RayOrthogonality.globalUnits M≤Hr) (base η:Character)
    (θ:RayQuotient.Characters M Hr) (z:O) (hz:z≠0)
    (pool:Finset Id) (W:Id→ℂ) (t P:ℝ) :
    naturalSlot (bareCharacter z)
      (QRH.SilDensitySplit.CubeFree.FP.RestoredInitialSource.supportedPool pool)
      (heightCoefficient (fun I=>idealCoeff (relativeCharacter M Hr hHr (base.product η.inverse) θ) I*W I) t) P =
    CenteredMomentWholeSlotDeletion.normalizedSlot η (fixedBadMask*idealGenerator 1) 1 z pool
      (fun I=>idealCoeff (relativeCharacter M Hr hHr base θ) I*W I) t P := by
  rw [QRH.SilDensitySplit.CubeFree.FP.RestoredInitialSource.supported_naturalSlot (bareCharacter z)
    (QRH.SilDensitySplit.CubeFree.FP.RestoredInitialSource.natural_character_off_supported bareBase z hz)]
  exact bare_compensated_original_slot M Hr hHr base η θ z hz pool W t P

theorem bare_product_ideal (η:Character) (z:O) (hz:z≠0) (I:Id) :
    idealCoeff ((bareCharacter z).product η) I=idealCoeff (naturalCharacter η z) I := by
  rw [idealCoeff_product,bare_character_ideal z hz I,naturalCharacter_eq η z hz,(naturalRow η z hz).ideal]
  ring

theorem original_zero_polynomial (η:Character) (z:O) (hz:z≠0)
    (W:ℝ→ℂ) (X:ℝ) (hX:0<X) :
    QRH.Cycle092.OrdinaryColumn.original η (fixedBadMask*idealGenerator 1) 1 z W 0 X =
      HeckeDyadic.polynomial (naturalCharacter η z) false W X 0 0 := by
  unfold QRH.Cycle092.OrdinaryColumn.original
  rw [(naturalRow η z hz).masked_plain 1 one_ne_zero,naturalCharacter_eq η z hz,
    plain_zero_height _ W X hX]
  simp only [CenteredMomentHeckeTwist.twistedIdealSum,CenteredMomentHeckeCancellation.idealSum,
    Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one,excluded_one_ideal]

#print axioms bare_character_ideal
#print axioms bare_compensated_original_slot
#print axioms original_zero_polynomial
end
end QRH.Cycle092.ColoredRootRestore
