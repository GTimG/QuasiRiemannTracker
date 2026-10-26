/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Cycle63.Physical
noncomputable section

/-- A fixed power loss in the scale is harmless on the large external-height
range. The extra integer degree is chosen before the scale and height. -/
theorem exists_external_height_degree {τ : ℝ} (hτ : 0<τ) (extra ε : ℝ) :
    ∃ n : ℕ, ∀ Z H m : ℝ, 1≤Z → Z^τ≤H →
      Z^(m+extra) ≤ H^n*Z^(m+ε) := by
  obtain ⟨n,hn⟩ := exists_nat_ge ((extra-ε)/τ)
  have hdegree : extra-ε≤τ*(n:ℝ) := by
    have hh := (div_le_iff₀ hτ).mp hn
    simpa only [mul_comm] using hh
  refine ⟨n,?_⟩
  intro Z H m hZ hH
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hZp.le τ) hH n
  calc
    _ ≤ Z^((m+ε)+τ*n) :=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    _ = (Z^τ)^n*Z^(m+ε) := by
      rw [Real.rpow_add hZp,Real.rpow_mul_natCast hZp.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hZp.le _)

/-- Combine the bounded-height analytic estimate and a genuine all-height
coarse estimate. No threshold may depend on the live external height. -/
theorem extend_bounded_height_bound {τ : ℝ} (hτ : 0<τ) (extra ε : ℝ)
    (jSmall jCoarse : ℕ) :
    ∃ j : ℕ, ∀ Z H m E control Csmall Ccoarse : ℝ,
      1≤Z → 1≤H → 0≤control → 0≤Csmall → 0≤Ccoarse →
      (H≤Z^τ → E≤Csmall*control*H^jSmall*Z^(m+ε)) →
      E≤Ccoarse*control*H^jCoarse*Z^(m+extra) →
      E≤(Csmall+Ccoarse)*control*H^j*Z^(m+ε) := by
  obtain ⟨n,hn⟩ := exists_external_height_degree hτ extra ε
  let j := max jSmall (jCoarse+n)
  refine ⟨j,?_⟩
  intro Z H m E control Csmall Ccoarse hZ hH hc hCs hCc hsmall hcoarse
  have hHp : 0≤H := zero_le_one.trans hH
  have hZp : 0≤Z^(m+ε) := Real.rpow_nonneg (zero_le_one.trans hZ) _
  by_cases hb : H≤Z^τ
  · apply (hsmall hb).trans
    apply mul_le_mul_of_nonneg_right _ hZp
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (by linarith : Csmall≤Csmall+Ccoarse) hc)
      (pow_le_pow_right₀ hH (le_max_left _ _)) (pow_nonneg hHp _) (by positivity)
  · have hlarge := hn Z H m hZ (le_of_not_ge hb)
    have hbnd := hcoarse.trans (mul_le_mul_of_nonneg_left hlarge
      (mul_nonneg (mul_nonneg hCc hc) (pow_nonneg hHp _)))
    have heq : Ccoarse*control*H^jCoarse*(H^n*Z^(m+ε)) =
        Ccoarse*control*H^(jCoarse+n)*Z^(m+ε) := by rw [pow_add];ring
    rw [heq] at hbnd
    apply hbnd.trans
    apply mul_le_mul_of_nonneg_right _ hZp
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (by linarith : Ccoarse≤Csmall+Ccoarse) hc)
      (pow_le_pow_right₀ hH (le_max_right _ _)) (pow_nonneg hHp _) (by positivity)

end
end Cycle63.Physical

#print axioms Cycle63.Physical.exists_external_height_degree
#print axioms Cycle63.Physical.extend_bounded_height_bound
