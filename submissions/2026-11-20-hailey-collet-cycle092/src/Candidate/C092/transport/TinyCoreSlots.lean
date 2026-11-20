/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Absolute bounds for the actual original prime slots, with no response premise. -/
import Candidate.C092.transport.TinyCorePayment

set_option autoImplicit false
namespace QRH.Cycle092.TinyCore
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open HeckeFamily HeckePrimeAnnular HeckeDyadic CenteredMomentHeckeSlots CenteredMomentCoreFloor
open QRH.Cycle092.WholeSlot
local notation "O" => HeckeFamily.O

/-- A single actual profile bound precedes the slot scales, ray multipliers
and all heights. Positive sigma makes the annular norm weight at most one. -/
theorem original_slot_coefficient_bound (W : ℝ → ℂ) (hW : Continuous W)
    (hs : Function.support W ⊆ Set.Icc (1 : ℝ) 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ (χ : Character) (D σ freq : ℝ) (I : Ideal O),
      0 < D → 0 ≤ σ →
      ‖idealCoeff χ I*annularWeight W D σ freq I‖ ≤ B := by
  obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (by norm_num : (1 : ℝ) ≤ 2)) hW.norm.continuousOn
  let B := 1+‖W x‖
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro χ D σ freq I hD hσ
  by_cases hz : W ((I.absNorm : ℝ)/D) = 0
  · simp [annularWeight,hz,hB.le]
  · have hy := hs hz
    have hypos : 0 < (I.absNorm : ℝ)/D := zero_lt_one.trans_le hy.1
    have hpow : ‖(((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-shift σ freq)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hypos]
      simpa only [Complex.neg_re,shift_re] using Real.rpow_le_one_of_one_le_of_nonpos hy.1 (neg_nonpos.mpr hσ)
    have hwb : ‖W ((I.absNorm : ℝ)/D)‖ ≤ B := (hmax hy).trans (by dsimp [B]; linarith)
    have hw : ‖annularWeight W D σ freq I‖ ≤ B := by
      rw [annularWeight,norm_mul]
      exact (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans (by simpa using hwb)
    rw [norm_mul]
    exact (mul_le_mul (idealCoeff_norm_le_one χ I) hw (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- The original prime support, rather than the whole ambient ideal set,
retains its actual norm cap for every nonzero marked coefficient. -/
theorem original_slot_norm_cap (W : ℝ → ℂ)
    (hs : Function.support W ⊆ Set.Icc (1 : ℝ) 2)
    (χ : Character) (D σ freq : ℝ) (I : Ideal O) (hD : 0 < D)
    (hne : idealCoeff χ I*annularWeight W D σ freq I ≠ 0) :
    (I.absNorm : ℝ) ≤ 2*D := by
  have hW : W ((I.absNorm : ℝ)/D) ≠ 0 := by
    intro hz
    exact hne (by simp [annularWeight,hz])
  exact (div_le_iff₀ hD).1 (hs hW).2

/-- Actual squared whole-slot factors cost only their original P, uniformly
on every row, with no assumption on the measured response or zero band. -/
theorem slot_product_absolute {Slot : Type*} [Fintype Slot]
    (η : Character) (mask A z : O) (t B : ℝ) (hB : 0 ≤ B)
    (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ) (P : Slot → ℝ)
    (hP : ∀ i, 0 < P i)
    (hcoeff : ∀ i I, I ∈ pool i → ‖coeff i I‖ ≤ B)
    (hcap : ∀ i I, I ∈ pool i → coeff i I ≠ 0 → (I.absNorm : ℝ) ≤ 2*P i) :
    (∏ i, ‖rowSlot η mask A z (pool i) (coeff i) t‖^2/P i) ≤
      ((256*B)^2)^(Fintype.card Slot)*(∏ i, P i) := by
  have hslot (i : Slot) : ‖rowSlot η mask A z (pool i) (coeff i) t‖ ≤ (256*B)*P i := by
    have h := rowSlot_bound η mask A z (pool i) (coeff i) t (2*P i) B
      (mul_nonneg (by norm_num) (hP i).le) hB (hcoeff i) (hcap i)
    convert h using 1 <;> ring
  have hsquare (i : Slot) : ‖rowSlot η mask A z (pool i) (coeff i) t‖^2/P i ≤ (256*B)^2*P i := by
    apply (div_le_iff₀ (hP i)).2
    have h := pow_le_pow_left₀ (norm_nonneg _) (hslot i) 2
    nlinarith only [h]
  calc
    _ ≤ ∏ i, (256*B)^2*P i := Finset.prod_le_prod₀ (fun i _ => div_nonneg (sq_nonneg _) (hP i).le) (fun i _ => hsquare i)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]

end
end QRH.Cycle092.TinyCore
