import Candidate.Cycle63.Physical.FinalErrorCapacity.Physical
import Candidate.Cycle63.Physical.TerminalLedger

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63FinalErrorCapacity
noncomputable section
open Cycle63.AffineLedger
open HeckeFamily CompletedGauss CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

theorem actual_prime_widths (p : O) (hp : p ≠ 0) (Z : ℝ) (hZ : 1 < Z)
    (k : ℕ) (hk : 1 ≤ k) :
    errorRemoval p Z k = (k:ℝ)*Real.logb Z ((Ideal.span {p}).absNorm:ℝ) ∧
      0 ≤ errorMoving p Z k ∧ errorMoving p Z k ≤ errorRemoval p Z k := by
  have hQ := Ideal.span_singleton_eq_bot.not.mpr hp
  have hn := CenteredMomentAmplificationChildSourceCaps.norm_ge_one (Ideal.span {p}) hQ
  have hl : 0 ≤ Real.logb Z (normValue p) := Real.logb_nonneg hZ hn
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  constructor
  · rfl
  · unfold errorMoving errorRemoval
    split_ifs <;> constructor <;> nlinarith

variable [Cycle63.AffineLedger] in
/-- The width defect is paid at the same global deletion rate as the
 original retained energy. Outside extraction and squared scalar costs
 remain separate, so the three literal alternatives can be substituted. -/
theorem paid_error_excess_bound {b M widthDefect allowance F w wo scalarLoss padding : ℝ}
    (hb : Cycle63.AffineLedger.firstCellTop≤b ∧ b≤Cycle63.AffineLedger.slotTop) (hM : 0 ≤ M)
    (hd : widthDefect ≤ allowance) (hallowance : 0 ≤ allowance)
    (hwo : wo ≤ w) (hpadding : 0 ≤ padding)
    (hF : F ≤ M*g b+3*(M*amp b)+(w-wo)+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-(w-wo)-scalarLoss ≤
      M*g b/6+M*amp b/2-(5/6)*(w-wo)-scalarLoss+padding/6 := by
  have hpaid := Cycle63.Physical.paid_deletion_bound (F := F) hd hallowance
    (show 0 ≤ (1/6:ℝ) ∧ (1/6:ℝ) ≤ 1 by norm_num)
  have hcap : 0 ≤ M*g b+3*(M*amp b)+(w-wo)+padding := by
    have hg := g_pos hb
    have ha := amp_pos hb
    have hw : 0 ≤ w-wo := sub_nonneg.mpr hwo
    positivity
  have hmax := max_le hF hcap
  linarith

variable [Cycle63.AffineLedger] in
theorem first_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : Cycle63.AffineLedger.firstCellTop≤b ∧ b≤Cycle63.AffineLedger.slotTop) (hM : 0 ≤ M)
    (hd : widthDefect ≤ allowance) (hallowance : 0 ≤ allowance)
    (hprime : primeFraction*(M*amp b) ≤ primeWidth) (hpadding : 0 ≤ padding)
    (hF : F ≤ M*g b+3*(M*amp b)+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-primeWidth ≤
      -M*firstErrorReserve+padding/6 := by
  have hp := paid_error_excess_bound (F := F) (w := primeWidth) (wo := primeWidth)
    (scalarLoss := primeWidth) hb hM hd hallowance le_rfl hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (first_error_reserve hb) hM
  nlinarith

variable [Cycle63.AffineLedger] in
theorem sixth_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : Cycle63.AffineLedger.firstCellTop≤b ∧ b≤Cycle63.AffineLedger.slotTop) (hM : 0 ≤ M)
    (hd : widthDefect ≤ allowance) (hallowance : 0 ≤ allowance)
    (hprime : primeFraction*(M*amp b) ≤ primeWidth) (hpadding : 0 ≤ padding)
    (hF : F ≤ M*g b+3*(M*amp b)+6*primeWidth+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-6*primeWidth ≤
      -M*sixthErrorReserve+padding/6 := by
  have ha := amp_pos hb
  have hf := half_lt_primeFraction
  have hl : 0 ≤ primeWidth := le_trans (mul_nonneg (by linarith) (mul_nonneg hM ha.le)) hprime
  have hp := paid_error_excess_bound (F := F) (w := 6*primeWidth) (wo := 0) (scalarLoss := 0)
    hb hM hd hallowance (by linarith) hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (sixth_error_reserve hb) hM
  nlinarith

variable [Cycle63.AffineLedger] in
theorem seventh_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : Cycle63.AffineLedger.firstCellTop≤b ∧ b≤Cycle63.AffineLedger.slotTop) (hM : 0 ≤ M)
    (hd : widthDefect ≤ allowance) (hallowance : 0 ≤ allowance)
    (hprime : primeFraction*(M*amp b) ≤ primeWidth) (hpadding : 0 ≤ padding)
    (hF : F ≤ M*g b+3*(M*amp b)+6*primeWidth+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-7*primeWidth ≤
      -M*seventhErrorReserve+padding/6 := by
  have ha := amp_pos hb
  have hf := half_lt_primeFraction
  have hl : 0 ≤ primeWidth := le_trans (mul_nonneg (by linarith) (mul_nonneg hM ha.le)) hprime
  have hp := paid_error_excess_bound (F := F) (w := 7*primeWidth) (wo := primeWidth)
    (scalarLoss := primeWidth) hb hM hd hallowance (by linarith) hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (seventh_error_reserve hb) hM
  nlinarith

end
end OAI.SevenEighths.Cycle63FinalErrorCapacity
