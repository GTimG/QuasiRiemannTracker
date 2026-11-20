/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform original profile moment coefficient, keeping polynomial heights visible. -/
import Candidate.C092.transport.MixedMiddleReturnFinal
set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeDyadic

def paidMoment (Cs Cf Csource diag : ℝ) (degree Jw : ℕ)
    (U height Hw window : ℝ) : ℝ :=
  max 1 (Cs*((1+2*window*Real.log U)*(Cf*Csource*diag*(1+height)^degree*(1+Hw)^(2*Jw+1))+1))
def paidMomentConstant (Cs Cf Csource diag : ℝ) : ℝ := 1+Cs*(Cf*Csource*diag+1)
def paidMomentDegree (degree Jw : ℕ) : ℕ := degree+(2*Jw+1)

/-- The live Fourier window is bounded by the fixed authentic source hull.
All physical/witness heights remain a polynomial of their actual height. -/
theorem paid_moment_coefficient {Cs Cf Csource diag U height Hw window : ℝ} {degree Jw : ℕ}
    (hCs : 0 ≤ Cs) (hCf : 0 ≤ Cf) (hC : 0 ≤ Csource) (hdiag : 0 ≤ diag)
    (hU : 1 ≤ U) (hh : 0 ≤ height) (hHw : 0 ≤ Hw) (hfreq : Hw ≤ height)
    (hw : window ≤ RawTicket.nHi) :
    paidMoment Cs Cf Csource diag degree Jw U height Hw window ≤
      paidMomentConstant Cs Cf Csource diag*(1+2*RawTicket.nHi*Real.log U)*
        (1+height)^(paidMomentDegree degree Jw) := by
  let H := (1+height)^(paidMomentDegree degree Jw)
  let A := Cf*Csource*diag
  let L := 1+2*RawTicket.nHi*Real.log U
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hL : 1 ≤ L := by
    have hn : 0 ≤ RawTicket.nHi := by norm_num [RawTicket.nHi]
    dsimp [L];have hl := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hn) (Real.log_nonneg hU);linarith
  have hH : 1 ≤ H := one_le_pow₀ (by linarith : 1 ≤ 1+height)
  have hp : (1+height)^degree*(1+Hw)^(2*Jw+1) ≤ H := by
    calc
      _ ≤ (1+height)^degree*(1+height)^(2*Jw+1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith : 1+Hw ≤ 1+height) _)
          (by positivity)
      _ = _ := (pow_add _ _ _).symm
  have hwindow : 1+2*window*Real.log U ≤ L := by
    dsimp [L]
    have hh := mul_le_mul_of_nonneg_right (by linarith : 2*window ≤ 2*RawTicket.nHi) (Real.log_nonneg hU)
    linarith
  have hterm : (1+2*window*Real.log U)*(Cf*Csource*diag*(1+height)^degree*(1+Hw)^(2*Jw+1)) ≤ L*(A*H) := by
    apply (mul_le_mul_of_nonneg_right hwindow (by positivity)).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    convert mul_le_mul_of_nonneg_left hp hA using 1 <;> dsimp [A] <;> ring
  have hprod : 1 ≤ L*H := one_le_mul_of_one_le_of_one_le hL hH
  unfold paidMoment paidMomentConstant
  apply max_le
  · dsimp only [H,A,L] at *
    nlinarith [mul_nonneg hCs (show 0 ≤ Cf*Csource*diag+1 by positivity)]
  · have h := mul_le_mul_of_nonneg_left (add_le_add_right hterm 1) hCs
    dsimp only [H,A,L] at *
    nlinarith [mul_nonneg hCs (show 0 ≤ Cf*Csource*diag+1 by positivity),
      mul_nonneg hCs (show 0 ≤ (1+2*RawTicket.nHi*Real.log U)*(1+height)^(paidMomentDegree degree Jw)-1 by linarith)]

/-- A logarithmic window costs one arbitrarily small fixed power and a
fixed coefficient. The polynomial height is never spent as an exponent. -/
theorem paid_log_window {U sigma : ℝ} (hU : 1 ≤ U) (hs : 0<sigma) :
    1+2*RawTicket.nHi*Real.log U ≤ (1+2*RawTicket.nHi/sigma)*U^sigma := by
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hn : 0 ≤ RawTicket.nHi := by norm_num [RawTicket.nHi]
  have hl := Real.log_le_rpow_div hUp.le hs
  have hp := Real.one_le_rpow hU hs.le
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*RawTicket.nHi by positivity)
  calc
    _ ≤ U^sigma+2*RawTicket.nHi*(U^sigma/sigma) := add_le_add hp hm
    _ = _ := by ring

#print axioms paid_moment_coefficient
#print axioms paid_log_window
end
end QRH.Cycle092.MixedMiddleReturn
