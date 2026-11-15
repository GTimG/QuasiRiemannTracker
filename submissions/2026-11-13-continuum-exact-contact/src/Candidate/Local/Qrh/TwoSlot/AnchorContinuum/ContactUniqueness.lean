/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Uniqueness of the exact contact on the intended positive branch. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.AlgebraicContact

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section
open Set

def logRatio (x : ℝ) : ℝ :=
  Real.log (3888*19^5)+4*Real.log (15*x-13)+5*Real.log (1-x)-Real.log 7-
    4*Real.log (7-6*x)-5*Real.log (9*x-7)
def rate (x : ℝ) : ℝ := 60/(15*x-13)-5/(1-x)+24/(7-6*x)-45/(9*x-7)

theorem logRatio_deriv {x : ℝ} (hx : x ∈ Ioo (13/15:ℝ) (7/8)) :
    HasDerivAt logRatio (rate x) x := by
  have ha : 0 < 15*x-13 := by linarith [hx.1]
  have hb : 0 < 1-x := by linarith [hx.2]
  have hc : 0 < 7-6*x := by linarith [hx.2]
  have hd : 0 < 9*x-7 := by linarith [hx.1]
  have h1 := (((hasDerivAt_id x).const_mul 15).sub_const 13).log ha.ne'
  have h2 := ((hasDerivAt_id x).const_sub 1).log hb.ne'
  have h3 := (((hasDerivAt_id x).const_mul 6).const_sub 7).log hc.ne'
  have h4 := (((hasDerivAt_id x).const_mul 9).sub_const 7).log hd.ne'
  convert (((((h1.const_mul 4).const_add (Real.log (3888*19^5))).add
    (h2.const_mul 5)).sub_const (Real.log 7)).sub (h3.const_mul 4)).sub
    (h4.const_mul 5) using 1
  · funext y
    simp only [logRatio,Pi.sub_apply,Pi.add_apply,id_eq]
  · simp only [rate,id_eq]
    ring

theorem rate_pos {x : ℝ} (hx : x ∈ Ioo (13/15:ℝ) (7/8)) : 0 < rate x := by
  have ha : 0 < 15*x-13 := by linarith [hx.1]
  have hb : 0 < 1-x := by linarith [hx.2]
  have hc : 0 < 7-6*x := by linarith [hx.2]
  have hd : 0 < 9*x-7 := by linarith [hx.1]
  have h1 : (480:ℝ) ≤ 60/(15*x-13) := (le_div_iff₀ ha).mpr (by linarith [hx.2])
  have h2 : (5:ℝ)/(1-x) ≤ 40 := (div_le_iff₀ hb).mpr (by linarith [hx.2])
  have h3 : 0 < (24:ℝ)/(7-6*x) := div_pos (by norm_num) hc
  have h4 : (45:ℝ)/(9*x-7) ≤ 225/4 := (div_le_iff₀ hd).mpr (by linarith [hx.1])
  unfold rate
  linarith

theorem logRatio_strictMono : StrictMonoOn logRatio (Ioo (13/15:ℝ) (7/8)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo _ _)
  · intro x hx
    exact (logRatio_deriv hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (logRatio_deriv (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    exact rate_pos (interior_subset hx)

theorem logRatio_zero_of_root {x : ℝ} (hx : x ∈ Ioo (13/15:ℝ) (7/8))
    (hroot : polynomial x = 0) : logRatio x = 0 := by
  have ha : 15*x-13 ≠ 0 := ne_of_gt (by linarith [hx.1])
  have hb : 1-x ≠ 0 := ne_of_gt (by linarith [hx.2])
  have hc : 7-6*x ≠ 0 := ne_of_gt (by linarith [hx.2])
  have hd : 9*x-7 ≠ 0 := ne_of_gt (by linarith [hx.1])
  have he : 3888*19^5*(15*x-13)^4*(1-x)^5 = 7*(7-6*x)^4*(9*x-7)^5 := by
    unfold polynomial at hroot
    linarith
  have hh := congrArg Real.log he
  rw [Real.log_mul (mul_ne_zero (by norm_num) (pow_ne_zero 4 ha)) (pow_ne_zero 5 hb),
    Real.log_mul (by norm_num) (pow_ne_zero 4 ha),
    Real.log_mul (mul_ne_zero (by norm_num) (pow_ne_zero 4 hc)) (pow_ne_zero 5 hd),
    Real.log_mul (by norm_num) (pow_ne_zero 4 hc)] at hh
  simp only [Real.log_pow] at hh
  unfold logRatio
  norm_num only [show (3888:ℝ)*19^5 = 9627072912 by norm_num]
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem root_unique {x : ℝ} (hx : x ∈ Ioo (13/15:ℝ) (7/8))
    (hroot : polynomial x = 0) : x = theta := by
  apply logRatio_strictMono.injOn hx theta_range
  rw [logRatio_zero_of_root hx hroot,logRatio_zero_of_root theta_range theta_root]

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.root_unique
