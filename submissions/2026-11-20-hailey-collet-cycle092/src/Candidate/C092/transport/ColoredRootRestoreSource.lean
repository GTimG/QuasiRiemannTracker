/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The surviving native signed family on each actual shortened ordinary arm. -/
import Candidate.C092.transport.ColoredRootRestoreDomains
import Candidate.C092.transport.ColoredRootRestoreMarks
import Candidate.C092.transport.ColoredRootRestoreComplete
import Candidate.C092.transport.RegularColoredForwardPolynomial

set_option autoImplicit false
namespace QRH.Cycle092.ColoredRootRestore
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion CenteredMomentSourceMass
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial CenteredMomentSecondHeightFamily
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower.KernelAssignmentReindex Candidate.FourthPower.KernelCollisionEnergy
open QRH.SilDensitySplit.CubeFree.FP.KernelRowExpansion
open QRH.SilDensitySplit.CubeFree.FP.KernelRowProfiles
open QRH.SilDensitySplit.CubeFree.FP.KernelRowPools
open QRH.SilDensitySplit.CubeFree.FP.KernelMarkedRows
open QRH.SilDensitySplit.CubeFree.FP.ReferencePrimeEnclosure
open QRH.SilDensitySplit.CubeFree.FP.RestoredInitialSource
open QRH.Cycle092.RegularColoredForward QRH.Cycle092.TwistedRawBallRootProducer
open QRH.Cycle092.OrdinaryColumn
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
variable {α:Type*} [Fintype α]

theorem signed_residual_sources (χ:Character) (ω₁ ω₂:Id→*₀ℂ) (S:Finset PrimeIdeal)
    (pool:α→Finset Id) (β:α→Id→ℂ) (P:α→ℝ) (W₁ W₂:ℝ→ℂ)
    {b X₁ X₂ Y₁ Y₂ M₁ M₂:ℝ} {d:IdealPair}
    (hb:0≤b) (hX₁:0<X₁) (hX₂:0<X₂) (hY₁:0<Y₁) (hY₂:0<Y₂)
    (hx₁:X₁≤M₁) (hx₂:X₂≤M₂) (hy₁:Y₁≤M₁) (hy₂:Y₂≤M₂)
    (hs₁:Function.support W₁⊆Set.Iic b) (hs₂:Function.support W₂⊆Set.Iic b)
    (hd:d∈divisorPool (supportedRectangle S b M₁ M₂)) :
    signedRow false S χ ω₁ ω₂ pool β P (residualPool (supportedRectangle S b M₁ M₂) d)
      W₁ W₂ (X₁/d.1.absNorm) (X₂/d.2.absNorm) (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) 1 1 =
    restoredRow χ ω₁ ω₂ S pool β P W₁ W₂ b (X₁/d.1.absNorm) (X₂/d.2.absNorm)-
      restoredRow χ ω₁ ω₂ S pool β P W₁ W₂ b (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) := by
  unfold signedRow restoredRow restoredRowOn
  simp only [one_mul]
  have hxe : weightedSum (naturalCoefficients χ S pool β P)
      (fun slot=>row χ ω₁ ω₂ (residualPool (supportedRectangle S b M₁ M₂) d)
        (sourceValue false S slot) W₁ W₂ (X₁/d.1.absNorm) (X₂/d.2.absNorm)) =
      weightedSum (naturalCoefficients χ S pool β P)
      (fun slot=>row χ ω₁ ω₂ (supportedRectangle S b (X₁/d.1.absNorm) (X₂/d.2.absNorm))
        (sourceValue false S slot) W₁ W₂ (X₁/d.1.absNorm) (X₂/d.2.absNorm)) := by
    unfold weightedSum
    apply Finset.sum_congr rfl
    intro slot hslot
    dsimp only
    rw [residual_row_domain χ ω₁ ω₂ S _ W₁ W₂ hb hX₁ hX₂ hx₁ hx₂ hs₁ hs₂ hd]
  have hye : weightedSum (naturalCoefficients χ S pool β P)
      (fun slot=>row χ ω₁ ω₂ (residualPool (supportedRectangle S b M₁ M₂) d)
        (sourceValue false S slot) W₁ W₂ (Y₁/d.1.absNorm) (Y₂/d.2.absNorm)) =
      weightedSum (naturalCoefficients χ S pool β P)
      (fun slot=>row χ ω₁ ω₂ (supportedRectangle S b (Y₁/d.1.absNorm) (Y₂/d.2.absNorm))
        (sourceValue false S slot) W₁ W₂ (Y₁/d.1.absNorm) (Y₂/d.2.absNorm)) := by
    unfold weightedSum
    apply Finset.sum_congr rfl
    intro slot hslot
    dsimp only
    rw [residual_row_domain χ ω₁ ω₂ S _ W₁ W₂ hb hY₁ hY₂ hy₁ hy₂ hs₁ hs₂ hd]
  rw [hxe,hye]

/-- The bare natural sextic anchor carries neither original ordinary
character. Each is restored on its own coordinate, including ramified zeros. -/
theorem bare_pair_row_physical (η₁ η₂:Character) (z:O) (hz:z≠0)
    (S:Finset PrimeIdeal) (W₁ W₂:ℝ→ℂ) {b X₁ X₂:ℝ}
    (hX₁:0<X₁) (hX₂:0<X₂)
    (hs₁:Function.support W₁⊆Set.Iic b) (hs₂:Function.support W₂⊆Set.Iic b)
    (henclose:∀ I:Id,Supported I → ((I.absNorm:ℝ)≤b*X₁ ∨ (I.absNorm:ℝ)≤b*X₂) →
      primeSupport I⊆primeValues S) :
    row (bareCharacter z) (idealCoeff η₁) (idealCoeff η₂)
      (supportedRectangle S b X₁ X₂) (fun _=>1) W₁ W₂ X₁ X₂ =
    original η₁ (fixedBadMask*idealGenerator 1) 1 z W₁ 0 X₁*
      original η₂ (fixedBadMask*idealGenerator 1) 1 z W₂ 0 X₂ := by
  unfold row
  rw [enclosed_row (bareCharacter z) S b X₁ X₂ _ _ _
    (natural_character_off_supported bareBase z hz) henclose]
  change row (bareCharacter z) (idealCoeff η₁) (idealCoeff η₂)
    (rectangle b X₁ X₂) (fun _=>1) W₁ W₂ X₁ X₂ = _
  rw [QRH.Cycle092.RegularColoredForward.natural_pair_row _ η₁ η₂ W₁ W₂ b X₁ X₂ hX₁ hX₂ hs₁ hs₂,
    original_zero_polynomial η₁ z hz W₁ X₁ hX₁,original_zero_polynomial η₂ z hz W₂ X₂ hX₂]
  rw [HeckeDetectorCoefficientTransfer.polynomial_eq_of_idealCoeff _ _ (bare_product_ideal η₁ z hz),
    HeckeDetectorCoefficientTransfer.polynomial_eq_of_idealCoeff _ _ (bare_product_ideal η₂ z hz)]

theorem bare_pair_common_row_physical (η₁ η₂:Character) (z:O) (hz:z≠0)
    (S:Finset PrimeIdeal) (W₁ W₂:ℝ→ℂ) {b X₁ X₂ M₁ M₂:ℝ}
    (hb:0≤b) (hX₁:0<X₁) (hX₂:0<X₂) (h₁:X₁≤M₁) (h₂:X₂≤M₂)
    (hs₁:Function.support W₁⊆Set.Iic b) (hs₂:Function.support W₂⊆Set.Iic b)
    (henclose:∀ I:Id,Supported I → ((I.absNorm:ℝ)≤b*M₁ ∨ (I.absNorm:ℝ)≤b*M₂) →
      primeSupport I⊆primeValues S) :
    row (bareCharacter z) (idealCoeff η₁) (idealCoeff η₂)
      (supportedRectangle S b M₁ M₂) (fun _=>1) W₁ W₂ X₁ X₂ =
    original η₁ (fixedBadMask*idealGenerator 1) 1 z W₁ 0 X₁*
      original η₂ (fixedBadMask*idealGenerator 1) 1 z W₂ 0 X₂ := by
  rw [row_common_domain _ _ _ S _ W₁ W₂ hb hX₁ hX₂ h₁ h₂ hs₁ hs₂]
  exact bare_pair_row_physical η₁ η₂ z hz S W₁ W₂ hX₁ hX₂ hs₁ hs₂ (by
    intro I hI hi
    apply henclose I hI
    rcases hi with hi|hi
    · exact Or.inl (hi.trans (mul_le_mul_of_nonneg_left h₁ hb))
    · exact Or.inr (hi.trans (mul_le_mul_of_nonneg_left h₂ hb)))

/-- Exact physical-mark norm identification. The source base is the actual
first base compensated by eta1.inverse. The ordinary colors remain eta1,eta2. -/
theorem fullSigned_physical_norm
    (M:Id) [NeZero M] (Hr:Subgroup (O⧸M)ˣ)
    (hHr:RayOrthogonality.globalUnits M≤Hr) (base η₁ η₂:Character)
    (θ:α→RayQuotient.Characters M Hr) (z:O) (hz:z≠0)
    (S:Finset PrimeIdeal) (pool:α→Finset Id) (slotWeight:α→Id→ℂ) (P:α→ℝ)
    (mark:α→ℂ) (tMark:ℝ) (W₁ W₂:ℝ→ℂ) {b M₁ M₂ X₁ X₂ Y₁ Y₂:ℝ}
    (hb:0≤b) (hX₁:0<X₁) (hX₂:0<X₂) (hY₁:0<Y₁) (hY₂:0<Y₂)
    (hx₁:X₁≤M₁) (hx₂:X₂≤M₂) (hy₁:Y₁≤M₁) (hy₂:Y₂≤M₂)
    (hs₁:Function.support W₁⊆Set.Iic b) (hs₂:Function.support W₂⊆Set.Iic b)
    (henclose:∀ I:Id,Supported I → ((I.absNorm:ℝ)≤b*M₁ ∨ (I.absNorm:ℝ)≤b*M₂) →
      primeSupport I⊆primeValues S)
    (hmark:∀ i,‖mark i‖=‖CenteredMomentWholeSlotDeletion.normalizedSlot η₁
      (fixedBadMask*idealGenerator 1) 1 z (pool i)
      (fun I=>idealCoeff (CenteredMomentNaturalFixedRaySource.relativeCharacter M Hr hHr base (θ i)) I*slotWeight i I)
      tMark (P i)‖) :
    ‖fullSigned S (bareCharacter z) (idealCoeff η₁) (idealCoeff η₂)
      (fun i=>supportedPool (pool i))
      (fun i=>heightCoefficient (fun I=>idealCoeff (CenteredMomentNaturalFixedRaySource.relativeCharacter M Hr hHr
        (base.product η₁.inverse) (θ i)) I*slotWeight i I) tMark) P
      (supportedRectangle S b M₁ M₂) W₁ W₂ X₁ X₂ Y₁ Y₂ 1 1‖ =
    ‖(original η₁ (fixedBadMask*idealGenerator 1) 1 z W₁ 0 X₁*
        original η₂ (fixedBadMask*idealGenerator 1) 1 z W₂ 0 X₂-
      original η₁ (fixedBadMask*idealGenerator 1) 1 z W₁ 0 Y₁*
        original η₂ (fixedBadMask*idealGenerator 1) 1 z W₂ 0 Y₂)*∏ i,mark i‖ := by
  unfold fullSigned
  simp only [one_mul]
  rw [bare_pair_common_row_physical η₁ η₂ z hz S W₁ W₂ hb hX₁ hX₂ hx₁ hx₂ hs₁ hs₂ henclose,
    bare_pair_common_row_physical η₁ η₂ z hz S W₁ W₂ hb hY₁ hY₂ hy₁ hy₂ hs₁ hs₂ henclose,
    norm_mul,norm_mul,norm_prod,norm_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [bare_compensated_supported_original_slot M Hr hHr base η₁ (θ i) z hz]
  exact (hmark i).symm

#print axioms signed_residual_sources
#print axioms bare_pair_row_physical
#print axioms fullSigned_physical_norm
end
end QRH.Cycle092.ColoredRootRestore
