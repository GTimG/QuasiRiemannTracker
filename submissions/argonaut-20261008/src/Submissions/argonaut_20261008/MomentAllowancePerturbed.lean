import Mathlib

namespace OAI.SevenEighths.PerturbedMomentAllowance

noncomputable def gamma (beta : ℝ) : ℝ := max 0 (beta - 7 / 8)
noncomputable def kappaPlain (beta : ℝ) : ℝ := 3 / 4 + 2 * gamma beta

theorem gamma_nonneg (beta : ℝ) : 0 ≤ gamma beta := le_max_left _ _

theorem gamma_le_eighth {beta : ℝ} (hbeta : beta ≤ 1) : gamma beta ≤ 1 / 8 := by
  apply max_le
  · norm_num
  · linarith

theorem kappaPlain_ge_three_quarters (beta : ℝ) : 3 / 4 ≤ kappaPlain beta := by
  dsimp [kappaPlain]
  linarith [gamma_nonneg beta]

theorem kappaPlain_ge_zero_capacity (beta : ℝ) :
    2 * beta - 1 ≤ kappaPlain beta := by
  have h := le_max_right (0 : ℝ) (beta - 7 / 8)
  dsimp [kappaPlain, gamma] at *
  linarith

theorem kappaPlain_le_one {beta : ℝ} (hbeta : beta ≤ 1) :
    kappaPlain beta ≤ 1 := by
  dsimp [kappaPlain]
  linarith [gamma_le_eighth hbeta]

/-- The moment allowance is nonnegative even below the old boundary.
This is only a scalar comparison; it does not construct actual moments. -/
theorem relative_allowance_cost {rho beta H : ℝ}
    (hrho : 0 ≤ rho) (hbeta : 7 / 8 - rho / 4 ≤ beta) (hH : H ≤ 1) :
    -(beta - 7 / 8) + H * gamma beta / 4 ≤ rho / 4 := by
  by_cases hb : 7 / 8 ≤ beta
  · have hg : gamma beta = beta - 7 / 8 := by
      dsimp [gamma]
      exact max_eq_right (by linarith)
    have hprod : H * gamma beta ≤ gamma beta := by
      simpa using mul_le_mul_of_nonneg_right hH (gamma_nonneg beta)
    rw [hg] at hprod ⊢
    linarith
  · have hg : gamma beta = 0 := by
      dsimp [gamma]
      exact max_eq_left (by linarith)
    rw [hg]
    linarith

theorem concrete_boundary_allowance_cost {beta : ℝ}
    (hbeta : (3499999 : ℝ) / 4000000 < beta) :
    -(beta - 7 / 8) + (13 / 16 + 3 / 2000000) * gamma beta / 4 ≤
      1 / 4000000 := by
  have h := relative_allowance_cost (rho := (1 : ℝ) / 1000000)
    (beta := beta) (H := 13 / 16 + 3 / 2000000)
    (by norm_num) (by linarith) (by norm_num)
  norm_num at h ⊢
  exact h

#print axioms gamma_nonneg
#print axioms gamma_le_eighth
#print axioms kappaPlain_ge_three_quarters
#print axioms kappaPlain_ge_zero_capacity
#print axioms kappaPlain_le_one
#print axioms relative_allowance_cost
#print axioms concrete_boundary_allowance_cost

end OAI.SevenEighths.PerturbedMomentAllowance
