import Candidate.Target836.SourceProvider.ErrorNamed
import Candidate.Cycle63.Physical.FinalErrorCapacity.Physical
import Candidate.Cycle63.Physical.TerminalLedger

set_option autoImplicit false
namespace Target874836.SourceProvider.ErrorCapacity
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63FinalErrorCapacity
open HeckeFamily CompletedGauss CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

theorem actual_prime_widths (p : O) (hp : p ≠ 0) (Z : ℝ) (hZ : 1 < Z)
    (k : ℕ) (hk : 1  ≤  k) :
    errorRemoval p Z k = (k:ℝ)*Real.logb Z ((Ideal.span {p}).absNorm:ℝ) ∧
      0  ≤  errorMoving p Z k ∧ errorMoving p Z k  ≤  errorRemoval p Z k := by
  have hQ := Ideal.span_singleton_eq_bot.not.mpr hp
  have hn := CenteredMomentAmplificationChildSourceCaps.norm_ge_one (Ideal.span {p}) hQ
  have hl : 0  ≤  Real.logb Z (normValue p) := Real.logb_nonneg hZ hn
  have hk' : (1:ℝ)  ≤  k := by exact_mod_cast hk
  constructor
  · rfl
  · unfold errorMoving errorRemoval
    split_ifs <;> constructor <;> nlinarith

/-- The width defect is paid at the same global deletion rate as the
 original retained energy. Outside extraction and squared scalar costs
 remain separate, so the three literal alternatives can be substituted. -/
theorem paid_error_excess_bound {b M widthDefect allowance F w wo scalarLoss padding : ℝ}
    (hb : 3401/100000  ≤  b ∧ b  ≤  1/25) (hM : 0  ≤  M)
    (hd : widthDefect  ≤  allowance) (hallowance : 0  ≤  allowance)
    (hwo : wo  ≤  w) (hpadding : 0  ≤  padding)
    (hF : F  ≤  M*Named.errorGap b+3*(M*Named.amp b)+(w-wo)+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-(w-wo)-scalarLoss  ≤ 
      M*Named.errorGap b/6+M*Named.amp b/2-(5/6)*(w-wo)-scalarLoss+padding/6 := by
  have hpaid := Cycle63.Physical.paid_deletion_bound (F := F) hd hallowance
    (show 0  ≤  (1/6:ℝ) ∧ (1/6:ℝ)  ≤  1 by norm_num)
  have hcap : 0  ≤  M*Named.errorGap b+3*(M*Named.amp b)+(w-wo)+padding := by
    have hg := Named.errorGap_pos hb
    have ha := Named.amp_pos hb
    have hw : 0  ≤  w-wo := sub_nonneg.mpr hwo
    positivity
  have hmax := max_le hF hcap
  linarith

theorem first_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : 3401/100000  ≤  b ∧ b  ≤  1/25) (hM : 0  ≤  M)
    (hd : widthDefect  ≤  allowance) (hallowance : 0  ≤  allowance)
    (hprime : 3*(M*Named.amp b)/4  ≤  primeWidth) (hpadding : 0  ≤  padding)
    (hF : F  ≤  M*Named.errorGap b+3*(M*Named.amp b)+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-primeWidth  ≤ 
      -M*(1/1000)+padding/6 := by
  have hp := paid_error_excess_bound (F := F) (w := primeWidth) (wo := primeWidth)
    (scalarLoss := primeWidth) hb hM hd hallowance le_rfl hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (Named.first_error_reserve hb) hM
  nlinarith

theorem sixth_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : 3401/100000  ≤  b ∧ b  ≤  1/25) (hM : 0  ≤  M)
    (hd : widthDefect  ≤  allowance) (hallowance : 0  ≤  allowance)
    (hprime : 3*(M*Named.amp b)/4  ≤  primeWidth) (hpadding : 0  ≤  padding)
    (hF : F  ≤  M*Named.errorGap b+3*(M*Named.amp b)+6*primeWidth+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-6*primeWidth  ≤ 
      -M*(11360006033/482529600000)+padding/6 := by
  have ha := Named.amp_pos hb
  have hl : 0  ≤  primeWidth := by nlinarith
  have hp := paid_error_excess_bound (F := F) (w := 6*primeWidth) (wo := 0) (scalarLoss := 0)
    hb hM hd hallowance (by linarith) hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (Named.sixth_error_reserve hb) hM
  nlinarith

theorem seventh_paid_error_reserve {b M widthDefect allowance F primeWidth padding : ℝ}
    (hb : 3401/100000  ≤  b ∧ b  ≤  1/25) (hM : 0  ≤  M)
    (hd : widthDefect  ≤  allowance) (hallowance : 0  ≤  allowance)
    (hprime : 3*(M*Named.amp b)/4  ≤  primeWidth) (hpadding : 0  ≤  padding)
    (hF : F  ≤  M*Named.errorGap b+3*(M*Named.amp b)+6*primeWidth+padding) :
    widthDefect-allowance+(1/6)*max (F-widthDefect) 0-7*primeWidth  ≤ 
      -M*(3516816899/120632400000)+padding/6 := by
  have ha := Named.amp_pos hb
  have hl : 0  ≤  primeWidth := by nlinarith
  have hp := paid_error_excess_bound (F := F) (w := 7*primeWidth) (wo := primeWidth)
    (scalarLoss := primeWidth) hb hM hd hallowance (by linarith) hpadding (by linarith)
  have hr := mul_le_mul_of_nonneg_left (Named.seventh_error_reserve hb) hM
  nlinarith

#print axioms actual_prime_widths
#print axioms paid_error_excess_bound
#print axioms first_paid_error_reserve
#print axioms sixth_paid_error_reserve
#print axioms seventh_paid_error_reserve
end
end Target874836.SourceProvider.ErrorCapacity
