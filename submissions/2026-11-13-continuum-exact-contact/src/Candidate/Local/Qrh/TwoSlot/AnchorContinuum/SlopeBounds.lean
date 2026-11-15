/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Uniform sign and slope bounds for the continuum source subcurves. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.Convexity

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorContinuum.Curve
open Set

theorem forcing_nonpos {r : ℝ} (hr : 2/3 < r) (hr1 : r ≤ 7/9) : b r ≤ 0 := by
  unfold b
  exact div_nonpos_of_nonpos_of_nonneg (by linarith)
    (mul_nonneg (by linarith) (by linarith))

theorem D_seed (lam : ℝ) {T : ℝ} (hT : 2/3 < T) : D lam T T = lam*b T := by
  simp only [D,flow,Z_seed hT,mul_zero,zero_add]

theorem monotoneOn_D {lam T : ℝ} (hlam : 0 < lam) (hT : 3/4 ≤ T) :
    MonotoneOn (D lam T) (Icc (3/4:ℝ) T) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
  · intro r hr
    exact (continuousAt_D lam T (by linarith [hr.1])).continuousWithinAt
  · intro r hr
    have hh := interior_subset hr
    exact (hasDerivAt_D lam T (by linarith [hh.1])).hasDerivWithinAt
  · intro r hr
    have hh := interior_subset hr
    exact (DD_pos hlam (by linarith) (by linarith [hh.1])).le

theorem D_nonpos {lam T r : ℝ} (hlam : 0 < lam)
    (hT : 3/4 ≤ T) (hT1 : T ≤ 7/9) (hr : r ∈ Icc (3/4:ℝ) T) : D lam T r ≤ 0 := by
  have h := monotoneOn_D hlam hT hr ⟨hT,le_rfl⟩ hr.2
  rw [D_seed lam (by linarith)] at h
  exact h.trans (mul_nonpos_of_nonneg_of_nonpos hlam.le (forcing_nonpos (by linarith) hT1))

theorem D_neg {lam T r : ℝ} (hlam : 0 < lam)
    (hT : 3/4 ≤ T) (hT1 : T < 7/9) (hr : r ∈ Icc (3/4:ℝ) T) : D lam T r < 0 := by
  have h := monotoneOn_D hlam hT hr ⟨hT,le_rfl⟩ hr.2
  rw [D_seed lam (by linarith)] at h
  exact h.trans_lt (mul_neg_of_pos_of_neg hlam (forcing_neg (by linarith) hT1))

theorem antitoneOn_W {lam T : ℝ} (hlam : 0 < lam) (hT : 3/4 ≤ T) (hT1 : T ≤ 7/9) :
    AntitoneOn (W lam T) (Icc (3/4:ℝ) T) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
  · intro r hr
    exact (hasDerivAt_W lam T (by linarith [hr.1])).continuousAt.continuousWithinAt
  · intro r hr
    have hh := interior_subset hr
    exact (hasDerivAt_W lam T (by linarith [hh.1])).hasDerivWithinAt
  · intro r hr
    exact D_nonpos hlam hT hT1 (interior_subset hr)

theorem W_nonneg {lam T r : ℝ} (hlam : 0 < lam)
    (hT : 3/4 ≤ T) (hT1 : T ≤ 7/9) (hr : r ∈ Icc (3/4:ℝ) T) : 0 ≤ W lam T r := by
  have h := antitoneOn_W hlam hT hT1 hr ⟨hT,le_rfl⟩ hr.2
  simpa only [W_seed lam (T := T) (by linarith)] using h

theorem forcing_lower {r : ℝ} (hr : 3/4 ≤ r) : -(4/45:ℝ) ≤ b r := by
  have hden : 0 < r*(15*r-10) := mul_pos (by linarith) (by linarith)
  unfold b
  rw [le_div_iff₀ hden]
  have h := mul_nonneg (show 0 ≤ r-3/4 by linarith) (show 0 ≤ 60*r+140 by linarith)
  nlinarith only [h]

/-- The uniform slope range used by all limiting local-stage comparisons. -/
theorem D_bounds {lam T r : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hT : 3/4 ≤ T) (hT1 : T ≤ 7/9) (hr : r ∈ Icc (3/4:ℝ) T) :
    -(4/45:ℝ) ≤ D lam T r ∧ D lam T r ≤ 0 := by
  have hz : 0 ≤ Z T r := by
    simpa only [W,one_mul] using W_nonneg (lam := 1) (by norm_num) hT hT1 hr
  have hA : 0 ≤ A r := by
    unfold A
    exact add_nonneg (div_nonneg (by norm_num) (by linarith [hr.1]))
      (div_nonneg (by norm_num) (by linarith [hr.1]))
  have hpos := mul_nonneg hlam.le (mul_nonneg hA hz)
  have hneg := mul_nonneg_of_nonpos_of_nonpos (show lam-1 ≤ 0 by linarith)
    (forcing_nonpos (by linarith [hr.1]) (hr.2.trans hT1))
  have hb : b r ≤ D lam T r := by unfold D flow; nlinarith only [hpos,hneg]
  exact ⟨(forcing_lower hr.1).trans hb,D_nonpos hlam hT hT1 hr⟩

end Qrh.TwoSlot.AnchorContinuum.Curve
#print axioms Qrh.TwoSlot.AnchorContinuum.Curve.D_bounds
