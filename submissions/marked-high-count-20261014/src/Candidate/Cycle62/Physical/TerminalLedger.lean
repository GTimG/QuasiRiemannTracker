import Candidate.Cycle62.Arithmetic.LocalReserves

namespace Cycle62.Physical
noncomputable section
open Cycle62.Arithmetic

/-- The supported-width allowance is nonnegative, but the actual width
difference may be negative. This is the paid-deletion inequality (2.16). -/
theorem paid_deletion_bound {d δ F r : ℝ} (hd : d ≤ δ) (hδ : 0 ≤ δ)
    (hr : 0 ≤ r ∧ r ≤ 1) : d+r*max (F-d) 0 ≤ δ+r*max F 0 := by
  by_cases hFd : d ≤ F
  · rw [max_eq_left (sub_nonneg.mpr hFd)]
    have h₁ := mul_le_mul_of_nonneg_left hd (show 0 ≤ 1-r by linarith [hr.2])
    have h₂ := mul_le_mul_of_nonneg_left (le_max_left F 0) hr.1
    nlinarith [mul_nonneg hr.1 hδ]
  · rw [max_eq_right (show F-d ≤ 0 by linarith)]
    nlinarith [mul_nonneg hr.1 (le_max_right F 0)]

/-- After the actual width defect and greedy deletion have been paid, the
six-amplifier defect still leaves the strict low reserve. -/
theorem low_paid_excess_bound {b M d δ F padding : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hM : 0 ≤ M)
    (hd : d ≤ δ) (hδ : 0 ≤ δ) (hpad : 0 ≤ padding)
    (hF : F ≤ M*g b+6*(M*amp b)+padding) :
    d+(2*q0/9)*max (F-d) 0-δ-M*amp b ≤
      -M*(7/30000000)+(2*q0/9)*padding := by
  have hg := g_pos hb
  have ha := amp_pos hb
  have hcap : 0 ≤ M*g b+6*(M*amp b)+padding := by positivity
  have hmax := max_le hF hcap
  have hpaid := paid_deletion_bound (F := F) hd hδ
    (show 0 ≤ 2*q0/9 ∧ 2*q0/9 ≤ 1 by norm_num [q0])
  have hprod := mul_le_mul_of_nonneg_left hmax (show 0 ≤ 2*q0/9 by norm_num [q0])
  have hreserve := low_reserve b
  have hid : M*amp b-(2*q0/9)*(M*g b+6*(M*amp b)) = M*(7/30000000) := by
    calc
      _ = M*(amp b*(1-4*q0/3)-(2*q0/9)*g b) := by ring
      _ = _ := by rw [hreserve]
  linarith

/-- Pointwise form of (2.24); the maximum is reached at v=M/4. -/
theorem fixed_inducing_excess_bound (A M v : ℝ) :
    A-5*M/6-2*v/3-max (M/4-v) 0 ≤ A-M := by
  by_cases hv : v ≤ M/4
  · rw [max_eq_left (sub_nonneg.mpr hv)]
    linarith
  · rw [max_eq_right (show M/4-v ≤ 0 by linarith)]
    linarith

theorem fixed_inducing_excess_attained (A M : ℝ) :
    A-5*M/6-2*(M/4)/3-max (M/4-M/4) 0 = A-M := by
  simp only [sub_self, max_self]
  ring

theorem second_zero_excess_bound {b M A a c d Bc : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hM : 0 ≤ M)
    (hA : A ≤ M*totalA b) (ha : a ≤ M*amp b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hBc : 0 ≤ Bc) :
    A-M-min c d-Bc+5*a ≤ -M*(336582307/4825296000) := by
  have hreserve := mul_le_mul_of_nonneg_left (second_zero_reserve hb) hM
  have hmin : 0 ≤ min c d := le_min hc hd
  nlinarith

theorem main_fixed_excess_bound {b M A a v : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hM : 0 ≤ M)
    (hA : A ≤ M*totalA b) (ha : a ≤ M*amp b) :
    A-5*M/6-2*v/3-max (M/4-v) 0+4*a ≤ -M*(2477341073/30158100000) := by
  have hreserve := mul_le_mul_of_nonneg_left (main_fixed_reserve hb) hM
  have hbase := fixed_inducing_excess_bound A M v
  nlinarith

theorem error_fixed_excess_bound {b M A a v : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hM : 0 ≤ M)
    (hA : A ≤ M*totalA b) (ha : a ≤ M*amp b) :
    A-5*M/6-2*v/3-max (M/4-v) 0+9*a ≤ -M*(794401277/40210800000) := by
  have hreserve := mul_le_mul_of_nonneg_left (error_fixed_reserve hb) hM
  have hbase := fixed_inducing_excess_bound A M v
  nlinarith

end
end Cycle62.Physical

#print axioms Cycle62.Physical.low_paid_excess_bound
#print axioms Cycle62.Physical.fixed_inducing_excess_bound
#print axioms Cycle62.Physical.second_zero_excess_bound
#print axioms Cycle62.Physical.main_fixed_excess_bound
#print axioms Cycle62.Physical.error_fixed_excess_bound
