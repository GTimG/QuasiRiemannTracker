/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Nonnegative limiting margin throughout the complete admitted critical
rectangle, with strict positivity below maximum amplitude. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.QuadraticReturn

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section
open Set Qrh.TwoSlot.AnchorZeroLoss.Affine.Return

def a : ℝ := 1+2*exactLine.g1
def b : ℝ := 1+6*exactLine.g0-4*exactLine.g1
def q10 (h : ℝ) : ℝ := 2*a*(theta-1/2-ell/2)+5*ell-h*(2*a/3+5/8+(5/8)*b)
def q20 (h : ℝ) : ℝ := -a-(1+a)*(2*ell-h/4)+(3/4)*h*(2*a+b)
def q21 (h : ℝ) : ℝ := -2*a*(2*ell-h/4)
def amplitudeResidual (d p : ℝ) : ℝ :=
  d*(q10 stationaryCutoff+d*(q20 stationaryCutoff+q21 stationaryCutoff*p))

theorem ab_bounds : (11519/10000:ℝ) ≤ a ∧ a ≤ 11521/10000 ∧
    (10443/10000:ℝ) ≤ b ∧ b ≤ 2089/2000 := by
  have hc := tangent_coefficient_bounds
  dsimp [a,b,exactLine]
  constructor
  · linarith [hc.2.2.1]
  constructor
  · linarith [hc.2.2.2]
  constructor <;> linarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

theorem residual_coefficient_bounds : -(143/1000:ℝ) < q10 stationaryCutoff ∧
    (117/200:ℝ) < q20 stationaryCutoff ∧ -(331/1000:ℝ) < q21 stationaryCutoff := by
  have hc := ab_bounds
  have he := ell_bounds
  have hh := stationaryCutoff_bounds
  have ht : (43667/50000:ℝ) < theta ∧ theta < 17467/20000 := by
    have hi := theta_isolated
    norm_num [lower,upper] at hi
    constructor <;> linarith [hi.1,hi.2]
  have ha0 : 0 ≤ a := by linarith [hc.1]
  have hb0 : 0 ≤ 2*a/3+5/8+(5/8)*b := by linarith [hc.1,hc.2.2.1]
  have hm0 := mul_le_mul hc.1
    (show (57339/200000:ℝ) ≤ theta-1/2-ell/2 by linarith [ht.1,he.2])
    (by norm_num : (0:ℝ) ≤ 57339/200000) ha0
  have hm1 := mul_le_mul hh.2.le
    (show 2*a/3+5/8+(5/8)*b ≤ 2*(11521/10000:ℝ)/3+5/8+(5/8)*(2089/2000) by
      linarith [hc.2.1,hc.2.2.2]) hb0 (by norm_num : (0:ℝ) ≤ 102/125)
  have hD0 : 0 ≤ 2*ell-stationaryCutoff/4 := by linarith [he.1,hh.2]
  have hD1 : 2*ell-stationaryCutoff/4 ≤ (14283/100000:ℝ) := by linarith [he.2,hh.1]
  have hm2 := mul_le_mul (show 1+a ≤ 1+(11521/10000:ℝ) by linarith [hc.2.1]) hD1
    hD0 (by norm_num : (0:ℝ) ≤ 1+11521/10000)
  have hm3 := mul_le_mul hh.1.le
    (show 2*(11519/10000:ℝ)+10443/10000 ≤ 2*a+b by linarith [hc.1,hc.2.2.1])
    (by norm_num : (0:ℝ) ≤ 2*(11519/10000:ℝ)+10443/10000) stationaryCutoff_pos.le
  have hm4 := mul_le_mul hc.2.1 hD1 hD0 (by norm_num : (0:ℝ) ≤ 11521/10000)
  unfold q10 q20 q21
  refine ⟨?_,?_,?_⟩ <;> nlinarith only [hm0,hm1,hm2,hm3,hm4,he.1,hc.2.1]

theorem amplitude_split (h d p : ℝ) :
    margin h d p = margin h d (1/2)+(1/2-p)*d*(q10 h+d*(q20 h+q21 h*p)) := by
  unfold margin baseCost ExactWindow.NI ExactWindow.JI ExactWindow.UI ExactWindow.kI q10 q20 q21 a b
  ring

theorem amplitudeResidual_lower {d p : ℝ}
    (hd : d ∈ Icc (189/512:ℝ) (15/32)) (hp : p ∈ Icc (15/32:ℝ) (1/2)) :
    d/100 ≤ amplitudeResidual d p := by
  have hc := residual_coefficient_bounds
  have hm0 := mul_le_mul_of_nonneg_right hc.2.2.le (show 0 ≤ p by linarith [hp.1])
  have hi : (839/2000:ℝ) < q20 stationaryCutoff+q21 stationaryCutoff*p := by
    nlinarith [hc.2.1,hp.2]
  have hd0 : 0 ≤ d := by linarith [hd.1]
  have hm1 := mul_le_mul_of_nonneg_left hi.le hd0
  have hh : (1/100:ℝ) ≤ q10 stationaryCutoff+d*(q20 stationaryCutoff+q21 stationaryCutoff*p) := by
    nlinarith [hc.1,hd.1]
  have hm2 := mul_nonneg hd0 (sub_nonneg.mpr hh)
  unfold amplitudeResidual
  nlinarith only [hm2]

theorem critical_rectangle_factorization (d p : ℝ) :
    margin stationaryCutoff d p = curvature stationaryCutoff*(d-density)^2+
      (1/2-p)*amplitudeResidual d p := by
  rw [amplitude_split,maximum_amplitude_factorization]
  unfold amplitudeResidual
  ring

theorem critical_rectangle_nonnegative {d p : ℝ}
    (hd : d ∈ Icc (189/512:ℝ) (15/32)) (hp : p ∈ Icc (15/32:ℝ) (1/2)) :
    0 ≤ margin stationaryCutoff d p := by
  rw [critical_rectangle_factorization]
  have hR := amplitudeResidual_lower hd hp
  exact add_nonneg (mul_nonneg (by linarith [stationary_curvature_pos]) (sq_nonneg _))
    (mul_nonneg (by linarith [hp.2]) (by linarith [hd.1]))

theorem critical_rectangle_target_positive {target d p : ℝ} (ht : theta < target)
    (hd : d ∈ Icc (189/512:ℝ) (15/32)) (hp : p ∈ Icc (15/32:ℝ) (1/2)) :
    0 < targetMargin target stationaryCutoff d p := by
  rw [target_shift]
  have hdp : 0 ≤ d*p := mul_nonneg (by linarith [hd.1]) (by linarith [hp.1])
  exact add_pos_of_nonneg_of_pos (critical_rectangle_nonnegative hd hp)
    (mul_pos (mul_pos (ExactWindow.hJ hd hp) (by linarith)) (sub_pos.mpr ht))

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.critical_rectangle_nonnegative
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.critical_rectangle_target_positive
