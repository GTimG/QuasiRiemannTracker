/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite inverse-count/native height factors are paid after their true degrees
are fixed and before the bounded-frequency family is selected. -/
import Candidate.C092.transport.SourceInverseP6CloseUniformPaid

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped BigOperators

theorem terminal_sqrt_power {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C) (k : ℕ) :
    Real.sqrt (C*B^k) ≤ (C+1)*B^k := by
  have hp : 1 ≤ B^k := one_le_pow₀ hB
  have hx : 0 ≤ C*B^k := mul_nonneg hC (by positivity)
  have hs := Real.sq_sqrt hx
  have hs0 := Real.sqrt_nonneg (C*B^k)
  have h : Real.sqrt (C*B^k) ≤ C*B^k+1 := by nlinarith
  calc
    _ ≤ C*B^k+1 := h
    _ ≤ (C+1)*B^k := by nlinarith

/-- The exponent J+degree+1 comes from the actual two displayed P6 height
factors. Its finite maximum may therefore be fixed before choosing tau. -/
theorem terminal_inverse_height_payment
    {Z τ q hi hl tLong C Cy E : ℝ} (scale : ℝ) (J degree : ℕ) (I : ℕ)
    (hZ : 1 ≤ Z) (hτ : 0 ≤ τ) (hhi : 0 ≤ hi) (hhl : 0 ≤ hl)
    (hhiBound : hi ≤ (1+2*Real.pi+(3*I:ℕ))*Z^τ)
    (hhlBound : |tLong|+hl ≤ 2*Z^τ)
    (hscale : 0 ≤ scale) (hC : 0 ≤ C) (hCy : 0 ≤ Cy) (hE : 0 ≤ E) :
    Cy*Real.sqrt (scale*(1+hi)*(C*(1+hi)^J))*
      Real.sqrt (E*(1+|tLong|+hl)^degree)*Z^q ≤
    (Cy*(scale*C+1)*(E+1)*(2+2*Real.pi+(3*I:ℕ))^(J+1)*(3:ℝ)^degree)*
      Z^(q+τ*((J+degree+1:ℕ):ℝ)) := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hp : 1 ≤ Z^τ := Real.one_le_rpow hZ hτ
  have hK : 0 ≤ 2+2*Real.pi+(3*I:ℕ) := by positivity
  have hB : 1 ≤ 1+hi := by linarith
  have hA : 1 ≤ 1+|tLong|+hl := by linarith [abs_nonneg tLong]
  have hBup : 1+hi ≤ (2+2*Real.pi+(3*I:ℕ))*Z^τ := by nlinarith
  have hAup : 1+|tLong|+hl ≤ 3*Z^τ := by linarith
  have hs1 : Real.sqrt (scale*(1+hi)*(C*(1+hi)^J)) ≤
      (scale*C+1)*((2+2*Real.pi+(3*I:ℕ))*Z^τ)^(J+1) := by
    have heq : scale*(1+hi)*(C*(1+hi)^J) = (scale*C)*(1+hi)^(J+1) := by rw [pow_succ];ring
    rw [heq]
    exact (terminal_sqrt_power hB (by positivity) (J+1)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hBup _) (by positivity))
  have hs2 : Real.sqrt (E*(1+|tLong|+hl)^degree) ≤ (E+1)*(3*Z^τ)^degree :=
    (terminal_sqrt_power hA hE degree).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hAup _) (by positivity))
  calc
    _ ≤ Cy*((scale*C+1)*((2+2*Real.pi+(3*I:ℕ))*Z^τ)^(J+1))*
        ((E+1)*(3*Z^τ)^degree)*Z^q := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hs1 hCy) hs2
          (Real.sqrt_nonneg _) (by positivity)) (Real.rpow_nonneg hZp.le _)
    _ = _ := by
      rw [mul_pow,mul_pow,←Real.rpow_mul_natCast hZp.le,←Real.rpow_mul_natCast hZp.le]
      rw [show q+τ*((J+degree+1:ℕ):ℝ) = τ*((J+1:ℕ):ℝ)+(τ*(degree:ℝ)+q) by push_cast;ring]
      rw [Real.rpow_add hZp,Real.rpow_add hZp]
      ring

#print axioms terminal_inverse_height_payment
end
end QRH.Cycle092.StrongPair
