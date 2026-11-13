/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Convexity of the seed subcurves and their genuine previous-source tangent
minorants. These calculus lemmas do not assume a moment estimate. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.UniformStep
import Mathlib.Analysis.Convex.Deriv

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorContinuum.Curve
open Set Filter

def AD (r : ℝ) : ℝ := -(4/5)/r^2-(1/5)/(r-2/3)^2
def qD (r : ℝ) : ℝ := A r*q0 r
def qDD (r : ℝ) : ℝ := -(16/225)*q0 r/(r^2*(r-2/3)^2)
def slopeDef (lam T r : ℝ) : ℝ := lam*(11/16-(P T/q0 T)*qD r)
def DD (lam T r : ℝ) : ℝ := -lam*(P T/q0 T)*qDD r

theorem hasDerivAt_A {r : ℝ} (hr : 2/3 < r) : HasDerivAt A (AD r) r := by
  have hr0 : r ≠ 0 := ne_of_gt (by linarith)
  have hs : r-2/3 ≠ 0 := ne_of_gt (by linarith)
  convert ((hasDerivAt_const r (4/5:ℝ)).div (hasDerivAt_id r) hr0).add
    ((hasDerivAt_const r (1/5:ℝ)).div ((hasDerivAt_id r).sub_const (2/3)) hs) using 1
  · rfl
  · simp only [AD,id_eq,zero_mul,mul_one,zero_sub]
    ring

theorem hasDerivAt_qD {r : ℝ} (hr : 2/3 < r) : HasDerivAt qD (qDD r) r := by
  have hr0 : r ≠ 0 := ne_of_gt (by linarith)
  have hn3 : -2+r*3 ≠ 0 := by linarith
  have hpoly : 12-r*36+r^2*27 ≠ 0 := by
    have he : 12-r*36+r^2*27 = 3*(-2+r*3)^2 := by ring
    rw [he]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ hn3)
  convert (hasDerivAt_A hr).mul (hasDerivAt_q0 hr) using 1
  · rfl
  · unfold qDD AD A
    ring_nf
    field_simp [hr0,hn3]
    ring_nf
    field_simp [hpoly]
    <;> ring

theorem qDD_neg {r : ℝ} (hr : 2/3 < r) : qDD r < 0 := by
  have hr0 : r ≠ 0 := ne_of_gt (by linarith)
  have hs : r-2/3 ≠ 0 := ne_of_gt (by linarith)
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by norm_num) (q0_pos hr))
    (mul_pos (sq_pos_of_ne_zero hr0) (sq_pos_of_ne_zero hs))

theorem D_eq_slopeDef (lam T : ℝ) {r : ℝ} (hr : 2/3 < r) :
    D lam T r = slopeDef lam T r := by
  have hp := P_flow hr
  unfold flow at hp
  unfold D slopeDef qD flow Z
  rw [hp]
  ring

theorem hasDerivAt_D (lam T : ℝ) {r : ℝ} (hr : 2/3 < r) :
    HasDerivAt (D lam T) (DD lam T r) r := by
  have hs : HasDerivAt (slopeDef lam T) (DD lam T r) r := by
    convert ((hasDerivAt_const r (11/16:ℝ)).sub
      ((hasDerivAt_qD hr).const_mul (P T/q0 T))).const_mul lam using 1
    · rfl
    · unfold DD
      ring
  apply hs.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with x hx
  exact D_eq_slopeDef lam T hx

theorem DD_pos {lam T r : ℝ} (hlam : 0 < lam)
    (hT : 2/3 < T) (hr : 2/3 < r) : 0 < DD lam T r := by
  have hc : 0 < P T/q0 T := div_pos (by unfold P; linarith) (q0_pos hT)
  exact mul_pos_of_neg_of_neg
    (mul_neg_of_neg_of_pos (by linarith) hc) (qDD_neg hr)

/-- Convexity justifies every tangent minorant used to request preceding sources. -/
theorem convex_W {lam T : ℝ} (hlam : 0 < lam) (hT : 3/4 ≤ T) :
    ConvexOn ℝ (Icc (3/4:ℝ) T) (W lam T) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (f' := D lam T) (f'' := DD lam T)
  · intro r hr
    exact (hasDerivAt_W lam T (by linarith [hr.1])).continuousAt.continuousWithinAt
  · intro r hr
    have hh := interior_subset hr
    exact (hasDerivAt_W lam T (by linarith [hh.1])).hasDerivWithinAt
  · intro r hr
    have hh := interior_subset hr
    exact (hasDerivAt_D lam T (by linarith [hh.1])).hasDerivWithinAt
  · intro r hr
    have hh := interior_subset hr
    exact (DD_pos hlam (by linarith) (by linarith [hh.1])).le

theorem tangent_previous {lam T R x : ℝ} (hlam : 0 < lam) (hR : 3/4 ≤ R)
    (hRx : R < x) (hxT : x ≤ T) :
    W lam T R+D lam T R*(x-R) ≤ W lam T x := by
  have hc := convex_W hlam (show 3/4 ≤ T by linarith)
  have h := hc.le_slope_of_hasDerivAt ⟨hR,by linarith⟩ ⟨by linarith,hxT⟩ hRx
    (hasDerivAt_W lam T (by linarith))
  rw [slope_def_field] at h
  have hh := (le_div_iff₀ (sub_pos.mpr hRx)).mp h
  linarith

end Qrh.TwoSlot.AnchorContinuum.Curve
#print axioms Qrh.TwoSlot.AnchorContinuum.Curve.convex_W
#print axioms Qrh.TwoSlot.AnchorContinuum.Curve.tangent_previous
