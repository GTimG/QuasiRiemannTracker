/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact ordinary character/height dictionary for the two-color forward children. -/
import Candidate.C092.transport.RegularColoredForwardChildren

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonMaskEnergy
open CenteredMomentHeckeHeight CenteredMomentRetainedEnergy CenteredMomentLattice
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Both ordinary anchors multiply the same physical sextic character. This
is equality of all ideal coefficients, including every genuine zero. -/
theorem naturalCharacter_product (η ψ : Character) (z : O) (hz : z ≠ 0) (I : Id) :
    idealCoeff ((naturalCharacter η z).product ψ) I =
      idealCoeff (naturalCharacter (η.product ψ) z) I := by
  rw [idealCoeff_product,naturalCharacter_eq η z hz,
    naturalCharacter_eq (η.product ψ) z hz,(naturalRow η z hz).ideal,
    (naturalRow (η.product ψ) z hz).ideal,idealCoeff_product]
  ring

/-- Each ordinary factor has its own original outside height phase. The
norm dictionary is exact and is proved with the original normalization. -/
theorem ordinary_polynomial_norm (η : Character) (z : O) (hz : z ≠ 0)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    ‖HeckeDyadic.polynomial (naturalCharacter η z) false
      (normPowerProfile W a b ha hs hW t) X 0 0‖ =
      ‖(Real.sqrt X : ℂ)⁻¹ * rowTwistedSum η (fixedBadMask*OAI.ConcretePrimeRowBridge.idealGenerator 1)
        1 z W t X‖ := by
  have hunit (χ : Character) (V : ℝ → ℂ) :
      HeckeDyadic.polynomial (excluded χ 1) false V X 0 0 =
        HeckeDyadic.polynomial χ false V X 0 0 := by
    simp only [HeckeDyadic.polynomial,HeckeDyadic.summand,HeckeDyadic.coefficient,
      Bool.false_eq_true,ite_false,excluded_one_ideal]
  have h := original_positive_normalized (α:=Empty) (naturalRow η z hz) 1 one_ne_zero
    W W a b a b ha ha hs hs hW hW
    (fun i => nomatch i) (fun i => nomatch i) (fun i => nomatch i)
    (fun i => nomatch i) t X X hX hX
  rw [hunit,←naturalCharacter_eq η z hz] at h
  simp only [positiveSlotRow,Finset.univ_eq_empty,Finset.prod_empty,mul_one,
    Real.sqrt_mul hX.le,Complex.ofReal_mul,mul_inv_rev] at h
  have hn := congrArg norm h
  simp only [norm_mul,positive_height_phase_norm X t hX,one_mul] at hn
  rw [norm_mul]
  have hp := mul_nonneg (norm_nonneg ((Real.sqrt X : ℂ)⁻¹))
    (norm_nonneg (rowTwistedSum η (fixedBadMask*OAI.ConcretePrimeRowBridge.idealGenerator 1) 1 z W t X))
  nlinarith [norm_nonneg (HeckeDyadic.polynomial (naturalCharacter η z) false
    (normPowerProfile W a b ha hs hW t) X 0 0),
    norm_nonneg ((Real.sqrt X : ℂ)⁻¹ * rowTwistedSum η
      (fixedBadMask*OAI.ConcretePrimeRowBridge.idealGenerator 1) 1 z W t X)]

/-- The exact ordinary factor arising in C.7 is the original ordinary sum
at anchor η·ψ, with its own height and the original physical row. -/
theorem colored_ordinary_polynomial_norm (η ψ : Character) (z : O) (hz : z ≠ 0)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    ‖HeckeDyadic.polynomial ((naturalCharacter η z).product ψ) false
      (normPowerProfile W a b ha hs hW t) X 0 0‖ =
      ‖(Real.sqrt X : ℂ)⁻¹ * rowTwistedSum (η.product ψ)
        (fixedBadMask*OAI.ConcretePrimeRowBridge.idealGenerator 1) 1 z W t X‖ := by
  have hc : HeckeDyadic.polynomial ((naturalCharacter η z).product ψ) false
      (normPowerProfile W a b ha hs hW t) X 0 0 =
      HeckeDyadic.polynomial (naturalCharacter (η.product ψ) z) false
        (normPowerProfile W a b ha hs hW t) X 0 0 := by
    simp only [HeckeDyadic.polynomial,HeckeDyadic.summand,HeckeDyadic.coefficient,
      Bool.false_eq_true,ite_false,naturalCharacter_product η ψ z hz]
  rw [hc]
  exact ordinary_polynomial_norm (η.product ψ) z hz W a b ha hs hW t X hX

/-- The mark coefficient dictionary is exact at its own original height.
Any frozen holes may already be present in β. -/
theorem natural_slot_eq_original (η : Character) (z : O) (hz : z ≠ 0)
    (pool : Finset Id) (β : Id → ℂ) (t P : ℝ) :
    CenteredMomentCommonMaskExpansion.naturalSlot (naturalCharacter η z) pool
      (heightCoefficient β t) P =
      CenteredMomentWholeSlotDeletion.normalizedSlot η
        (fixedBadMask*OAI.ConcretePrimeRowBridge.idealGenerator 1) 1 z pool β t P := by
  have hu : IsUnit (OAI.ConcretePrimeRowBridge.idealGenerator (1 : Id)) :=
    Ideal.span_singleton_eq_top.mp (by simpa using OAI.ConcretePrimeRowBridge.span_idealGenerator (1 : Id))
  obtain ⟨v,hv⟩ := hu
  have hp : (OAI.ConcretePrimeRowBridge.idealGenerator (1 : Id))^6 = 1 := by
    rw [←hv]
    exact CanonicalUnitEuler.unit_pow_six v
  simp only [CenteredMomentCommonMaskExpansion.naturalSlot,
    CenteredMomentWholeSlotDeletion.normalizedSlot,CenteredMomentHeckeSlots.rowSlot,
    heightCoefficient,naturalCharacter_eq η z hz,(naturalRow η z hz).ideal,mul_pow,hp,mul_one,one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  ring

#print axioms natural_slot_eq_original
#print axioms naturalCharacter_product
#print axioms ordinary_polynomial_norm
#print axioms colored_ordinary_polynomial_norm
end
end QRH.Cycle092.RegularColoredForward
