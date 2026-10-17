/- Closed forms of Collet's coupled plane, and sign criteria that locate the class bound of the
top-row certificate. Released under Apache 2.0. -/
import Candidate.Cycle63.Optimization.TopRow
import Candidate.Cycle63.Certificate.Tactic

set_option autoImplicit false

namespace Cycle63.Optimization

noncomputable section

/-- The quadratic factor of the coupled plane; it has no real roots. -/
def planeQuadratic (q : ℝ) : ℝ := 24*q^2 - 34*q + 35

theorem planeQuadratic_pos (q : ℝ) : 0 < planeQuadratic q := by
  unfold planeQuadratic; nlinarith [sq_nonneg (q - 17/24)]

theorem weight_closed {q : ℝ} (h5 : (5:ℝ) - 2*q ≠ 0) (h9 : (9:ℝ) - 12*q ≠ 0) :
    weight q = 2*q*(22*q - 5)/((9 - 12*q)*(5 - 2*q)) := by
  have h5' := h5; ring_nf at h5'
  have h9' := h9; ring_nf at h9'
  unfold weight amplifierRatio density
  field_simp
  ring

theorem plane_sum_closed {q : ℝ} (h5 : (5:ℝ) - 2*q ≠ 0) (h9 : (9:ℝ) - 12*q ≠ 0) (c : ℝ) :
    q + c*weight q = q*((9 - 12*q)*(5 - 2*q) + 2*c*(22*q - 5))/((9 - 12*q)*(5 - 2*q)) := by
  have h5' := h5; ring_nf at h5'
  have h9' := h9; ring_nf at h9'
  rw [weight_closed h5 h9]
  field_simp

/-- The slope in closed form, `24 q (q + 5)/E(q)` with `E(q) = 24 q^2 - 34 q + 35`. -/
theorem slope_closed {q : ℝ} (h0 : 0 < q) (h1 : q < 3/4) :
    slope q = 24*q*(q + 5)/planeQuadratic q := by
  have h5 : (5:ℝ) - 2*q ≠ 0 := by linarith
  have h9 : (9:ℝ) - 12*q ≠ 0 := by linarith
  have hD : (9 - 12*q)*(5 - 2*q) ≠ 0 := mul_ne_zero h9 h5
  have hn := plane_sum_closed h5 h9 (9/2)
  have hw := plane_sum_closed h5 h9 1
  rw [one_mul] at hw
  unfold slope
  rw [hn, hw, div_div_div_cancel_right₀ hD, mul_div_mul_left _ _ h0.ne']
  unfold planeQuadratic
  congr 1 <;> ring

theorem rootPoly_intercept (lam B B' δ : ℝ) :
    rootPoly lam B' δ - rootPoly lam B δ =
      (B' - B)*(6*δ*((25/2*lam - 10 + (6 - 9*lam)*δ) + 9*lam*(5/6 - δ))) := by
  unfold rootPoly; ring

theorem rootPoly_mono_intercept {lam B B' δ : ℝ} (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) (hδ' : δ ≤ 5/6)
    (hd : 0 ≤ 25/2*lam - 10 + (6 - 9*lam)*δ) (hB : B ≤ B') :
    rootPoly lam B δ ≤ rootPoly lam B' δ := by
  have h := rootPoly_intercept lam B B' δ
  have hc : 0 ≤ 6*δ*((25/2*lam - 10 + (6 - 9*lam)*δ) + 9*lam*(5/6 - δ)) := by
    have : 0 ≤ 9*lam*(5/6 - δ) := by nlinarith
    positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hB) hc]

/-- The point where `boundAt` equals `L`. -/
def deltaL (lam L : ℝ) : ℝ := lam*(9*L - 7)/(7*lam + 11 - 6*lam*L - 12*L)

/-- At the point `deltaL lam L` the bound formula takes the value `L`. -/
theorem boundAt_deltaL {lam L : ℝ} (hlam : 0 < lam) (hL : 7/9 < L)
    (hK : 0 < 7*lam + 11 - 6*lam*L - 12*L) : boundAt lam (deltaL lam L) = L := by
  have hd : 0 < deltaL lam L := by
    unfold deltaL; apply div_pos _ hK; nlinarith
  have hden : 0 < 9*lam + 6*lam*deltaL lam L + 12*deltaL lam L := by positivity
  unfold boundAt
  rw [div_eq_iff hden.ne']
  have hKne := hK.ne'
  unfold deltaL
  generalize hk : 7*lam + 11 - 6*lam*L - 12*L = K at hKne ⊢
  field_simp
  rw [← hk]
  ring

theorem deltaStar_between {lam B x y : ℝ} (ha : rootA2 lam B < 0) (hxy : x < y)
    (hx : rootPoly lam B x < 0) (hy : 0 < rootPoly lam B y) :
    0 < rootDisc lam B ∧ x < deltaStar lam B ∧ deltaStar lam B < y := by
  have hdisc : 0 < rootDisc lam B := by
    unfold rootDisc
    apply discrim_pos_of_pos ha (t := y)
    rw [← rootPoly_eq_quadratic]
    exact hy
  have hroot := rootPoly_deltaStar ha.ne hdisc.le
  have hsv := rootPoly_deriv_deltaStar ha.ne
  have hs : 0 < 2*rootA2 lam B*deltaStar lam B + rootA1 lam B := by
    rw [hsv]; exact Real.sqrt_pos.mpr hdisc
  refine ⟨hdisc, ?_, ?_⟩
  · -- A concave quadratic that vanishes at the root, is negative at `x` and positive at `y` cannot
    -- have the root at or left of `x`.
    by_contra hc
    push Not at hc
    have hid : rootPoly lam B x * (y - deltaStar lam B) =
        rootPoly lam B (deltaStar lam B) * (y - x) + rootPoly lam B y * (x - deltaStar lam B)
          - rootA2 lam B * (x - deltaStar lam B) * (y - x) * (y - deltaStar lam B) := by
      simp only [rootPoly_eq_quadratic]; ring
    rw [hroot] at hid
    have h1 : 0 ≤ x - deltaStar lam B := by linarith
    have h2 : 0 < y - x := by linarith
    have h3 : 0 < y - deltaStar lam B := by linarith
    have h4 : 0 ≤ rootPoly lam B y * (x - deltaStar lam B) := mul_nonneg hy.le h1
    have h5 : 0 ≤ -rootA2 lam B * (x - deltaStar lam B) * (y - x) * (y - deltaStar lam B) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) h1) h2.le) h3.le
    have h6 : rootPoly lam B x * (y - deltaStar lam B) < 0 := mul_neg_of_neg_of_pos hx h3
    linarith
  · -- Left of the root the quadratic increases up to the root, where it vanishes.
    by_contra hc
    push Not at hc
    have hm := quadratic_mono_left (c := rootA0 lam) ha hc hs.le
    rw [← rootPoly_eq_quadratic, ← rootPoly_eq_quadratic] at hm
    linarith

/-- The class bound is above `L` when `rootPoly` is negative at the point where `boundAt` equals
`L` and positive at a larger point `y`. -/
theorem lt_thetaMin_of_signs {lam B L y : ℝ} (hlam : 1 < lam) (hB : 0 < B) (hL : 7/9 < L)
    (hK : 0 < 7*lam + 11 - 6*lam*L - 12*L) (hdl : deltaL lam L < y)
    (hlow : rootPoly lam B (deltaL lam L) < 0) (hhigh : 0 < rootPoly lam B y) :
    L < thetaMin lam B := by
  have ha : rootA2 lam B < 0 := by unfold rootA2; nlinarith
  obtain ⟨-, hlt, -⟩ := deltaStar_between ha hdl hlow hhigh
  have hdl0 : 0 < deltaL lam L := by
    unfold deltaL; apply div_pos _ hK; nlinarith
  have hbL := boundAt_deltaL (lam := lam) (by linarith) hL hK
  unfold thetaMin
  calc L = boundAt lam (deltaL lam L) := hbL.symm
    _ < _ := boundAt_lt (by linarith) hdl0.le hlt

end

end Cycle63.Optimization
