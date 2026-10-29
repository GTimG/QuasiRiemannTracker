/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.AdaptivePrice
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Lattice

/-! Pointwise retained slope on the actual source range [.57,.75].
The seven exact polynomial identities use the versioned nonlinear price
certificate. No sign is assumed for the derived quantity k(ν)-κ(ν).
No analytic packed supplier or selected-norm theorem is asserted here. -/
namespace Qrh.JointDetector.PointwisePrice
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.Hybrid

def q0 : ℝ := 57/100
theorem q0_pos : 0 < q0 := by norm_num [q0]
def amplitudeFloor : ℝ := 10011/20000
def amplitudeCutoff : ℝ := 1001/2000
def reserve : ℝ := 1/250
def k (ν : ℝ) : ℝ := 10*ν/(15-6*ν)
def curveNum (ν : ℝ) : ℝ := 9/50-33/250*ν+253/125*ν^2
def curveDen (ν : ℝ) : ℝ := 378/25-3881/125*ν+18*ν^2
def curve (ν : ℝ) : ℝ := curveNum ν/curveDen ν
def slope (ν : ℝ) : ℝ := max amplitudeFloor (curve ν)
def curveDerivNum (ν : ℝ) : ℝ :=
  (-33/250+2*(253/125)*ν)*curveDen ν-curveNum ν*(-3881/125+36*ν)
def curveDeriv (ν : ℝ) : ℝ := curveDerivNum ν/(curveDen ν)^2

namespace Certificates

def delta_denominator (ν : ℝ) : ℝ := (378/25:ℝ) + (-3881/125:ℝ)*ν + (18/1:ℝ)*ν^2
theorem delta_denominator_identity (ν : ℝ) :
    delta_denominator ν=bern2 (45332/3125:ℝ) (85913/25000:ℝ) (1959/1000:ℝ) ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) := by
  unfold delta_denominator bern2
  ring
theorem delta_denominator_pos {ν : ℝ} (hν : ν ∈ Icc (1/50:ℝ) (3/4:ℝ)) : 0 < delta_denominator ν := by
  have ht : 0 ≤ ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) := div_nonneg (by linarith [hν.1,q0_pos]) (by norm_num)
  have ht' : ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) ≤ 1 := (div_le_one (by norm_num)).2 (by linarith [hν.2])
  rw [delta_denominator_identity]
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < (1959/1000:ℝ))
    (bern2_ge ht ht' (by norm_num) (by norm_num) (by norm_num))

def delta_positive (ν : ℝ) : ℝ := (9/50:ℝ) + (-33/250:ℝ)*ν + (253/125:ℝ)*ν^2
theorem delta_positive_identity (ν : ℝ) :
    delta_positive ν=bern2 (27839/156250:ℝ) (7977/50000:ℝ) (2439/2000:ℝ) ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) := by
  unfold delta_positive bern2
  ring
theorem delta_positive_pos {ν : ℝ} (hν : ν ∈ Icc (1/50:ℝ) (3/4:ℝ)) : 0 < delta_positive ν := by
  have ht : 0 ≤ ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) := div_nonneg (by linarith [hν.1,q0_pos]) (by norm_num)
  have ht' : ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) ≤ 1 := (div_le_one (by norm_num)).2 (by linarith [hν.2])
  rw [delta_positive_identity]
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < (7977/50000:ℝ))
    (bern2_ge ht ht' (by norm_num) (by norm_num) (by norm_num))

def delta_less_than_nu (ν : ℝ) : ℝ := (-9/50:ℝ) + (3813/250:ℝ)*ν + (-4134/125:ℝ)*ν^2 + (18/1:ℝ)*ν^3
theorem delta_less_than_nu_identity (ν : ℝ) :
    delta_less_than_nu ν=bern3 (17493/156250:ℝ) (547911/156250:ℝ) (60923/50000:ℝ) (999/4000:ℝ) ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) := by
  unfold delta_less_than_nu bern3
  ring
theorem delta_less_than_nu_pos {ν : ℝ} (hν : ν ∈ Icc (1/50:ℝ) (3/4:ℝ)) : 0 < delta_less_than_nu ν := by
  have ht : 0 ≤ ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) := div_nonneg (by linarith [hν.1,q0_pos]) (by norm_num)
  have ht' : ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) ≤ 1 := (div_le_one (by norm_num)).2 (by linarith [hν.2])
  rw [delta_less_than_nu_identity]
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < (17493/156250:ℝ))
    (bern3_ge ht ht' (by norm_num) (by norm_num) (by norm_num) (by norm_num))

def e_denominator (ν : ℝ) : ℝ := (45/1:ℝ) + (-108/1:ℝ)*ν + (81/1:ℝ)*ν^2 + (-18/1:ℝ)*ν^3
theorem e_denominator_identity (ν : ℝ) :
    e_denominator ν=bern3 (669879/15625:ℝ) (86877/5000:ℝ) (243/40:ℝ) (63/32:ℝ) ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) := by
  unfold e_denominator bern3
  ring
theorem e_denominator_pos {ν : ℝ} (hν : ν ∈ Icc (1/50:ℝ) (3/4:ℝ)) : 0 < e_denominator ν := by
  have ht : 0 ≤ ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) := div_nonneg (by linarith [hν.1,q0_pos]) (by norm_num)
  have ht' : ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) ≤ 1 := (div_le_one (by norm_num)).2 (by linarith [hν.2])
  rw [e_denominator_identity]
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < (63/32:ℝ))
    (bern3_ge ht ht' (by norm_num) (by norm_num) (by norm_num) (by norm_num))

def delta_increasing (ν : ℝ) : ℝ := (4491/1250:ℝ) + (171018/3125:ℝ)*ν + (-944768/15625:ℝ)*ν^2
theorem delta_increasing_identity (ν : ℝ) :
    delta_increasing ν=bern2 (91076741/19531250:ℝ) (37117563/1562500:ℝ) (166023/15625:ℝ) ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) := by
  unfold delta_increasing bern2
  ring
theorem delta_increasing_pos {ν : ℝ} (hν : ν ∈ Icc (1/50:ℝ) (3/4:ℝ)) : 0 < delta_increasing ν := by
  have ht : 0 ≤ ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) := div_nonneg (by linarith [hν.1,q0_pos]) (by norm_num)
  have ht' : ((ν-(1/50:ℝ))/((3/4:ℝ)-(1/50:ℝ))) ≤ 1 := (div_le_one (by norm_num)).2 (by linarith [hν.2])
  rw [delta_increasing_identity]
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < (91076741/19531250:ℝ))
    (bern2_ge ht ht' (by norm_num) (by norm_num) (by norm_num))

def delta_derivative_below_three (ν : ℝ) : ℝ := (852813/1250:ℝ) + (-8973126/3125:ℝ)*ν + (71646251/15625:ℝ)*ν^2 + (-419148/125:ℝ)*ν^3 + (972/1:ℝ)*ν^4
theorem delta_derivative_below_three_identity (ν : ℝ) :
    delta_derivative_below_three ν=bern4 (1372774073360612643/40000000000000000:ℝ) (7374544679025279/500000000000000:ℝ) (141662344477539/25000000000000:ℝ) (4028722173/2500000000:ℝ) (887571/1000000:ℝ) ((ν-(10011/20000:ℝ))/((3/4:ℝ)-(10011/20000:ℝ))) := by
  unfold delta_derivative_below_three bern4
  ring
theorem delta_derivative_below_three_pos {ν : ℝ} (hν : ν ∈ Icc (10011/20000:ℝ) (3/4:ℝ)) : 0 < delta_derivative_below_three ν := by
  have ht : 0 ≤ ((ν-(10011/20000:ℝ))/((3/4:ℝ)-(10011/20000:ℝ))) := div_nonneg (by linarith [hν.1,q0_pos]) (by norm_num)
  have ht' : ((ν-(10011/20000:ℝ))/((3/4:ℝ)-(10011/20000:ℝ))) ≤ 1 := (div_le_one (by norm_num)).2 (by linarith [hν.2])
  rw [delta_derivative_below_three_identity]
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < (887571/1000000:ℝ))
    (bern4_ge ht ht' (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

def delta_below_amplitude_floor_until_seven_tenths (ν : ℝ) : ℝ := (1847079/250000:ℝ) + (-38522691/2500000:ℝ)*ν + (69859/10000:ℝ)*ν^2
theorem delta_below_amplitude_floor_until_seven_tenths_identity (ν : ℝ) :
    delta_below_amplitude_floor_until_seven_tenths ν=bern2 (5702488664859/4000000000000:ℝ) (58638723549/100000000000:ℝ) (313169/12500000:ℝ) ((ν-(10011/20000:ℝ))/((7/10:ℝ)-(10011/20000:ℝ))) := by
  unfold delta_below_amplitude_floor_until_seven_tenths bern2
  ring
theorem delta_below_amplitude_floor_until_seven_tenths_pos {ν : ℝ} (hν : ν ∈ Icc (10011/20000:ℝ) (7/10:ℝ)) : 0 < delta_below_amplitude_floor_until_seven_tenths ν := by
  have ht : 0 ≤ ((ν-(10011/20000:ℝ))/((7/10:ℝ)-(10011/20000:ℝ))) := div_nonneg (by linarith [hν.1,q0_pos]) (by norm_num)
  have ht' : ((ν-(10011/20000:ℝ))/((7/10:ℝ)-(10011/20000:ℝ))) ≤ 1 := (div_le_one (by norm_num)).2 (by linarith [hν.2])
  rw [delta_below_amplitude_floor_until_seven_tenths_identity]
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < (313169/12500000:ℝ))
    (bern2_ge ht ht' (by norm_num) (by norm_num) (by norm_num))

end Certificates

theorem q0_gt_floor : amplitudeFloor < q0 := by norm_num [amplitudeFloor,q0]
theorem amplitude_gap : amplitudeFloor-amplitudeCutoff=(1/20000:ℝ) := by
  norm_num [amplitudeFloor,amplitudeCutoff]
theorem k_den_pos {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) : 0 < 15-6*ν := by linarith [hν.2]
theorem k_range {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) : (95/193:ℝ) ≤ k ν ∧ k ν ≤ 5/7 := by
  have hl : (57/100:ℝ) ≤ ν := hν.1
  constructor
  · rw [k,le_div_iff₀ (k_den_pos hν)]; linarith
  · rw [k,div_le_iff₀ (k_den_pos hν)]; linarith [hν.2]
theorem k_mul_den {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) : k ν*(15-6*ν)=10*ν :=
  div_mul_cancel₀ _ (k_den_pos hν).ne'

theorem curve_den_pos {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) : 0 < curveDen ν := by
  have hp := Certificates.delta_denominator_pos
    (show ν ∈ Icc (1/50:ℝ) (3/4) from ⟨by dsimp [q0] at hν; linarith [hν.1,q0_pos],hν.2⟩)
  convert hp using 1 <;> unfold curveDen Certificates.delta_denominator <;> ring

theorem curve_mul_den {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) : curve ν*curveDen ν=curveNum ν :=
  div_mul_cancel₀ _ (curve_den_pos hν).ne'

theorem curve_pos {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) : 0 < curve ν := by
  have hp := Certificates.delta_positive_pos
    (show ν ∈ Icc (1/50:ℝ) (3/4) from ⟨by dsimp [q0] at hν; linarith [hν.1,q0_pos],hν.2⟩)
  have hn : 0 < curveNum ν := by
    convert hp using 1 <;> unfold curveNum Certificates.delta_positive <;> ring
  exact div_pos hn (curve_den_pos hν)

theorem curve_lt_nu {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) : curve ν < ν := by
  have hp := Certificates.delta_less_than_nu_pos
    (show ν ∈ Icc (1/50:ℝ) (3/4) from ⟨by dsimp [q0] at hν; linarith [hν.1,q0_pos],hν.2⟩)
  have he : Certificates.delta_less_than_nu ν=ν*curveDen ν-curveNum ν := by
    unfold Certificates.delta_less_than_nu curveDen curveNum
    ring
  rw [he] at hp
  apply (div_lt_iff₀ (curve_den_pos hν)).2
  linarith

theorem curve_count_den_pos {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) : 0 < 3-ν-2*curve ν :=
  AdaptivePrice.count_den_pos hν.2 (curve_lt_nu hν).le

theorem slope_bounds {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) :
    amplitudeFloor ≤ slope ν ∧ slope ν ≤ ν := by
  refine ⟨le_max_left _ _,max_le ?_ (curve_lt_nu hν).le⟩
  exact q0_gt_floor.le.trans hν.1

theorem slope_pos {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) : 0 < slope ν := by
  have ha : (0:ℝ) < amplitudeFloor := by norm_num [amplitudeFloor]
  exact ha.trans_le (slope_bounds hν).1


theorem curve_count_identity {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) :
    jointCountExponent ν (curve ν)=1-k ν-reserve := by
  have hk := k_mul_den hν
  have hc := curve_mul_den hν
  have hid : ((1-k ν-reserve)*(3-ν-2*curve ν)-3*(1-curve ν)*(1-ν))*(15-6*ν)=
      curveDen ν*curve ν-curveNum ν := by
    unfold curveDen curveNum reserve
    linear_combination -(3-ν-2*curve ν)*hk
  have hz : ((1-k ν-reserve)*(3-ν-2*curve ν)-3*(1-curve ν)*(1-ν))*(15-6*ν)=0 := by
    rw [hid]
    nlinarith
  have he := (mul_eq_zero.mp hz).resolve_right (k_den_pos hν).ne'
  rw [jointCountExponent_eq]
  apply (div_eq_iff (curve_count_den_pos hν).ne').mpr
  linarith

theorem count_at_slope {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) :
    jointCountExponent ν (slope ν) ≤ 1-k ν-reserve :=
  (AdaptivePrice.count_mono hν.2 (curve_lt_nu hν).le (slope_bounds hν).2
    (le_max_right _ _)).trans_eq (curve_count_identity hν)

theorem curve_hasDerivAt {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) :
    HasDerivAt curve (curveDeriv ν) ν := by
  have hN : HasDerivAt curveNum (-33/250+2*(253/125)*ν) ν := by
    convert (((hasDerivAt_id ν).const_mul (33/250:ℝ)).const_sub (9/50)).add
      (((hasDerivAt_id ν).pow 2).const_mul (253/125:ℝ)) using 1
    · ext x
      simp only [curveNum,Pi.add_apply,Pi.pow_apply,id_eq]
    · norm_num <;> ring
  have hD : HasDerivAt curveDen (-3881/125+36*ν) ν := by
    convert (((hasDerivAt_id ν).const_mul (3881/125:ℝ)).const_sub (378/25)).add
      (((hasDerivAt_id ν).pow 2).const_mul (18:ℝ)) using 1
    · ext x
      simp only [curveDen,Pi.add_apply,Pi.pow_apply,id_eq]
    · norm_num <;> ring
  exact (hN.div hD (curve_den_pos hν).ne').congr_deriv (by
    dsimp [curveDeriv,curveDerivNum])

theorem curve_derivative_mem {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) :
    curveDeriv ν ∈ Icc (0:ℝ) 3 := by
  have hg : ν ∈ Icc (1/50:ℝ) (3/4) := ⟨by dsimp [q0] at hν; linarith [hν.1,q0_pos],hν.2⟩
  have ha : ν ∈ Icc amplitudeFloor (3/4) := ⟨q0_gt_floor.le.trans hν.1,hν.2⟩
  have hp := Certificates.delta_increasing_pos hg
  have hu := Certificates.delta_derivative_below_three_pos ha
  have heN : curveDerivNum ν=Certificates.delta_increasing ν := by
    unfold curveDerivNum curveNum curveDen Certificates.delta_increasing
    ring
  have heU : 3*(curveDen ν)^2-curveDerivNum ν=Certificates.delta_derivative_below_three ν := by
    unfold curveDerivNum curveNum curveDen Certificates.delta_derivative_below_three
    ring
  have hD : 0 < (curveDen ν)^2 := sq_pos_of_pos (curve_den_pos hν)
  constructor
  · exact div_nonneg ((by rw [heN]; exact hp.le):0 ≤ curveDerivNum ν) hD.le
  · apply (div_le_iff₀ hD).2
    rw [← heU] at hu
    linarith

theorem curve_lipschitz {x y : ℝ} (hx : x ∈ Icc q0 (3/4)) (hy : y ∈ Icc q0 (3/4)) :
    |curve y-curve x| ≤ 3*|y-x| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f:=curve) (f':=curveDeriv)
    (fun ν hν => (curve_hasDerivAt hν).hasDerivWithinAt)
    (fun ν hν => by
      rw [Real.norm_eq_abs,abs_of_nonneg (curve_derivative_mem hν).1]
      exact (curve_derivative_mem hν).2)
    (convex_Icc q0 (3/4:ℝ)) hx hy
  simpa only [Real.norm_eq_abs] using hh

theorem slope_lipschitz {x y : ℝ} (hx : x ∈ Icc q0 (3/4)) (hy : y ∈ Icc q0 (3/4)) :
    |slope y-slope x| ≤ 3*|y-x| := by
  have hh := abs_max_sub_max_le_max amplitudeFloor (curve y) amplitudeFloor (curve x)
  have hbound : |slope y-slope x| ≤ |curve y-curve x| := by
    simpa only [slope,sub_self,abs_zero,max_eq_right (abs_nonneg (curve y-curve x))] using hh
  exact hbound.trans (curve_lipschitz hx hy)

theorem slope_continuousOn : ContinuousOn slope (Icc q0 (3/4)) :=
  continuousOn_const.sup (fun _ν hν => (curve_hasDerivAt hν).continuousAt.continuousWithinAt)

theorem slope_flat {ν : ℝ} (hν : ν ∈ Icc q0 (7/10)) : slope ν=amplitudeFloor := by
  have hg : ν ∈ Icc q0 (3/4) := ⟨hν.1,by linarith [hν.2]⟩
  have ha : ν ∈ Icc amplitudeFloor (7/10) := ⟨q0_gt_floor.le.trans hν.1,hν.2⟩
  have hp := Certificates.delta_below_amplitude_floor_until_seven_tenths_pos ha
  have he : Certificates.delta_below_amplitude_floor_until_seven_tenths ν=
      amplitudeFloor*curveDen ν-curveNum ν := by
    unfold Certificates.delta_below_amplitude_floor_until_seven_tenths amplitudeFloor curveDen curveNum
    ring
  rw [he] at hp
  apply max_eq_left
  apply (div_le_iff₀ (curve_den_pos hg)).2
  linarith


def extendedMSlope (ν : ℝ) : ℝ := k ν+(ν-slope ν)/10
theorem extensionCoeff_nonneg {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) : 0 ≤ ν-slope ν :=
  sub_nonneg.mpr (slope_bounds hν).2

theorem extendedMSlope_bounds {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) :
    0 ≤ extendedMSlope ν ∧ extendedMSlope ν ≤ 1034923/1400000 := by
  have hk := k_range hν
  have hs := slope_bounds hν
  have he := extensionCoeff_nonneg hν
  dsimp [extendedMSlope]
  dsimp [amplitudeFloor] at hs
  constructor <;> linarith [hν.2]

def g (ν P s M : ℝ) : ℝ := ν*P-k ν*M+slope ν*s+(ν-slope ν)*max (s-M/10) 0
theorem g_eq_max {ν : ℝ} (hν : ν ∈ Set.Icc (q0 : ℝ) (3/4))
    (P s M : ℝ) :
    g ν P s M = max
      (ν * P - k ν * M + slope ν * s)
      (ν * P - extendedMSlope ν * M + ν * s) := by
  have hc := (extensionCoeff_nonneg hν)
  by_cases hs : s - M/10 ≤ 0
  · rw [g, max_eq_right hs, mul_zero, add_zero, max_eq_left]
    dsimp [extendedMSlope]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc hs]
  · have hs' : 0 ≤ s - M/10 := (le_of_not_ge hs)
    rw [g, max_eq_left hs', max_eq_right]
    · dsimp [extendedMSlope]
      ring
    · dsimp [extendedMSlope]
      nlinarith [mul_nonneg hc hs']

private theorem max_le_max_add {a b a' b' e : ℝ}
    (ha : a' ≤ a + e) (hb : b' ≤ b + e) :
    max a' b' ≤ max a b + e := by
  apply max_le
  · linarith [le_max_left a b]
  · linarith [le_max_right a b]

private theorem linear_increment_le {a L : ℝ} (ha : |a| ≤ L) (δ : ℝ) :
    a * δ ≤ L * |δ| := by
  calc
    a * δ ≤ |a * δ| := le_abs_self _
    _ = |a| * |δ| := abs_mul _ _
    _ ≤ L * |δ| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)

theorem g_mono {ν : ℝ} (hν : ν ∈ Set.Icc (q0 : ℝ) (3/4))
    {P P' s s' M : ℝ} (hP : P' ≤ P) (hs : s' ≤ s) :
    g ν P' s' M ≤ g ν P s M := by
  rw [g_eq_max hν, g_eq_max hν]
  have hn : 0 ≤ ν := by linarith [hν.1,q0_pos]
  have hκ := (slope_pos hν).le
  apply max_le_max
  · linarith [mul_le_mul_of_nonneg_left hP hn,
      mul_le_mul_of_nonneg_left hs hκ]
  · linarith [mul_le_mul_of_nonneg_left hP hn,
      mul_le_mul_of_nonneg_left hs hn]

/-- Arbitrary real ordinary-width increments, including negative increments. -/
theorem g_lipP_all {ν : ℝ} (hν : ν ∈ Set.Icc (q0 : ℝ) (3/4))
    (P s M δ : ℝ) :
    g ν (P + δ) s M ≤ g ν P s M + (3/4 : ℝ) * |δ| := by
  have hn : 0 ≤ ν := by linarith [hν.1,q0_pos]
  have ha : |ν| ≤ (3/4 : ℝ) := by simpa only [abs_of_nonneg hn] using hν.2
  have hδ := linear_increment_le ha δ
  have he : g ν (P + δ) s M = g ν P s M + ν * δ := by
    dsimp [g]
    ring
  rw [he]
  linarith

/-- Arbitrary real slot-width increments, including negative increments. -/
theorem g_lipS_all {ν : ℝ} (hν : ν ∈ Set.Icc (q0 : ℝ) (3/4))
    (P s M δ : ℝ) :
    g ν P (s + δ) M ≤ g ν P s M + (3/4 : ℝ) * |δ| := by
  rw [g_eq_max hν, g_eq_max hν]
  have hn : 0 ≤ ν := by linarith [hν.1,q0_pos]
  have hκ := slope_bounds hν
  have ha : |ν| ≤ (3/4 : ℝ) := by simpa only [abs_of_nonneg hn] using hν.2
  have hb : |slope ν| ≤ (3/4 : ℝ) := by
    rw [abs_of_nonneg (slope_pos hν).le]
    exact hκ.2.trans hν.2
  apply max_le_max_add
  · linarith [linear_increment_le hb δ]
  · linarith [linear_increment_le ha δ]

/-- The ordinary-width field of the generic `Price` interface. -/
theorem g_lipP {ν : ℝ} (hν : ν ∈ Set.Icc (q0 : ℝ) (3/4))
    (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    g ν (P + δ) s M ≤ g ν P s M + (3/4 : ℝ) * δ := by
  simpa only [abs_of_nonneg hδ] using g_lipP_all hν P s M δ

/-- The slot-width field of the generic `Price` interface. -/
theorem g_lipS {ν : ℝ} (hν : ν ∈ Set.Icc (q0 : ℝ) (3/4))
    (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    g ν P (s + δ) M ≤ g ν P s M + (3/4 : ℝ) * δ := by
  simpa only [abs_of_nonneg hδ] using g_lipS_all hν P s M δ

/-- The envelope field has the exact global bound `1034923/1400000`, for either sign. -/
theorem g_lipM {ν : ℝ} (hν : ν ∈ Set.Icc (q0 : ℝ) (3/4))
    (P s M δ : ℝ) :
    g ν P s (M + δ) ≤ g ν P s M + (1034923/1400000 : ℝ) * |δ| := by
  rw [g_eq_max hν, g_eq_max hν]
  have hk := k_range hν
  have hm := extendedMSlope_bounds hν
  have ha : |-k ν| ≤ (1034923/1400000 : ℝ) := by
    rw [abs_neg, abs_of_nonneg (by linarith [hk.1])]
    linarith [hk.2]
  have hb : |-extendedMSlope ν| ≤ (1034923/1400000 : ℝ) := by
    rw [abs_neg, abs_of_nonneg hm.1]
    exact hm.2
  apply max_le_max_add
  · linarith [linear_increment_le ha δ]
  · linarith [linear_increment_le hb δ]

/-- A bound uniform in the density parameter; no width has a sign restriction. -/
theorem g_upper_bound {ν : ℝ} (hν : ν ∈ Set.Icc (q0 : ℝ) (3/4))
    (P s M : ℝ) :
    g ν P s M ≤ (3/4 : ℝ) * |P| + (3/4 : ℝ) * |s| + (1034923/1400000 : ℝ) * |M| := by
  have hP := g_lipP_all hν 0 s M P
  have hs := g_lipS_all hν 0 0 M s
  have hM := g_lipM hν 0 0 0 M
  have hz : g ν 0 0 0 = 0 := by simp [g]
  simp only [zero_add] at hP hs hM
  linarith



def highSup (q P s M : ℝ) : ℝ :=
  ⨆ ν : Set.Icc q (3/4 : ℝ), g ν P s M

theorem highSup_bdd {q : ℝ} (hq : (q0 : ℝ) ≤ q) (P s M : ℝ) :
    BddAbove (Set.range fun ν : Set.Icc q (3/4 : ℝ) => g ν P s M) := by
  refine ⟨(3/4 : ℝ) * |P| + (3/4 : ℝ) * |s| + (1034923/1400000 : ℝ) * |M|, ?_⟩
  rintro _ ⟨ν, rfl⟩
  exact g_upper_bound ⟨hq.trans ν.2.1, ν.2.2⟩ P s M

theorem le_highSup {q ν : ℝ} (hq : (q0 : ℝ) ≤ q)
    (hν : q ≤ ν) (hν' : ν ≤ 3/4) (P s M : ℝ) :
    g ν P s M ≤ highSup q P s M := by
  exact le_ciSup (f := fun ν : Set.Icc q (3/4 : ℝ) => g ν P s M)
    (highSup_bdd hq P s M) ⟨ν, hν, hν'⟩

theorem highSup_le {q P s M a : ℝ} (hq : q ≤ (3/4 : ℝ))
    (h : ∀ ν, q ≤ ν → ν ≤ 3/4 → g ν P s M ≤ a) :
    highSup q P s M ≤ a := by
  have : Nonempty (Set.Icc q (3/4 : ℝ)) := ⟨⟨3/4, hq, le_rfl⟩⟩
  exact ciSup_le fun ν => h ν ν.2.1 ν.2.2

theorem highSup_mono {q : ℝ} (hq : q ∈ Set.Icc (q0 : ℝ) (3/4))
    {P P' s s' M : ℝ} (hP : P' ≤ P) (hs : s' ≤ s) :
    highSup q P' s' M ≤ highSup q P s M := by
  apply highSup_le hq.2
  intro ν hν hν'
  exact (g_mono ⟨hq.1.trans hν, hν'⟩ hP hs).trans
    (le_highSup hq.1 hν hν' P s M)

theorem highSup_lipP {q : ℝ} (hq : q ∈ Set.Icc (q0 : ℝ) (3/4))
    (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    highSup q (P + δ) s M ≤ highSup q P s M + (3/4 : ℝ) * δ := by
  apply highSup_le hq.2
  intro ν hν hν'
  exact (g_lipP ⟨hq.1.trans hν, hν'⟩ P s M δ hδ).trans
    (add_le_add (le_highSup hq.1 hν hν' P s M) le_rfl)

theorem highSup_lipS {q : ℝ} (hq : q ∈ Set.Icc (q0 : ℝ) (3/4))
    (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    highSup q P (s + δ) M ≤ highSup q P s M + (3/4 : ℝ) * δ := by
  apply highSup_le hq.2
  intro ν hν hν'
  exact (g_lipS ⟨hq.1.trans hν, hν'⟩ P s M δ hδ).trans
    (add_le_add (le_highSup hq.1 hν hν' P s M) le_rfl)

theorem highSup_lipM {q : ℝ} (hq : q ∈ Set.Icc (q0 : ℝ) (3/4))
    (P s M δ : ℝ) :
    highSup q P s (M + δ) ≤ highSup q P s M + (1034923/1400000 : ℝ) * |δ| := by
  apply highSup_le hq.2
  intro ν hν hν'
  exact (g_lipM ⟨hq.1.trans hν, hν'⟩ P s M δ).trans
    (add_le_add (le_highSup hq.1 hν hν' P s M) le_rfl)

def jointPrice (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (q0 : ℝ) (3/4)) :
    QRH.SilDensitySplit.CubeFree.Price where
  f w P s M := max
    (QRH.SilDensitySplit.Density.lowPart B₀ L₀ c₀ (q w) P s M)
    (highSup (q w) P s M)
  nonneg w P s M := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1,q0_pos]
    exact le_max_of_le_left (mul_nonneg hq0 (deletionNeed_nonneg B₀ L₀ c₀ P s M))
  mono w P P' s s' M hP hs := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1,q0_pos]
    exact max_le_max
      (mul_le_mul_of_nonneg_left (deletionNeed_mono hL hP hs) hq0)
      (highSup_mono (hq w) hP hs)
  lip := needLip B₀ L₀ c₀
  lip_nonneg := zero_le_one.trans (one_le_needLip B₀ L₀ c₀)
  lipP w P s M δ hδ := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1,q0_pos]
    have hq1 : q w ≤ 1 := by linarith [(hq w).2]
    have hK := one_le_needLip B₀ L₀ c₀
    apply QRH.SilDensitySplit.Density.max_le_max_add
    · exact QRH.SilDensitySplit.Density.lowPart_lip hq0 hq1
        (mul_nonneg (by linarith : 0 ≤ needLip B₀ L₀ c₀) hδ)
        (deletionNeed_lipP hL hδ)
    · have hhigh := highSup_lipP (hq w) P s M δ hδ
      have hscale : (3/4 : ℝ) * δ ≤ needLip B₀ L₀ c₀ * δ :=
        mul_le_mul_of_nonneg_right (by linarith) hδ
      exact hhigh.trans (add_le_add le_rfl hscale)
  lipS w P s M δ hδ := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1,q0_pos]
    have hq1 : q w ≤ 1 := by linarith [(hq w).2]
    have hK := one_le_needLip B₀ L₀ c₀
    apply QRH.SilDensitySplit.Density.max_le_max_add
    · exact QRH.SilDensitySplit.Density.lowPart_lip hq0 hq1
        (mul_nonneg (by linarith : 0 ≤ needLip B₀ L₀ c₀) hδ)
        (deletionNeed_lipS hL hδ)
    · have hhigh := highSup_lipS (hq w) P s M δ hδ
      have hscale : (3/4 : ℝ) * δ ≤ needLip B₀ L₀ c₀ * δ :=
        mul_le_mul_of_nonneg_right (by linarith) hδ
      exact hhigh.trans (add_le_add le_rfl hscale)
  lipM w P s M δ := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1,q0_pos]
    have hq1 : q w ≤ 1 := by linarith [(hq w).2]
    have hK := one_le_needLip B₀ L₀ c₀
    apply QRH.SilDensitySplit.Density.max_le_max_add
    · exact QRH.SilDensitySplit.Density.lowPart_lip hq0 hq1
        (mul_nonneg (by linarith : 0 ≤ needLip B₀ L₀ c₀) (abs_nonneg δ))
        (deletionNeed_lipM hL)
    · have hhigh := highSup_lipM (hq w) P s M δ
      have hscale : (1034923/1400000 : ℝ) * |δ| ≤ needLip B₀ L₀ c₀ * |δ| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg δ)
      exact hhigh.trans (add_le_add le_rfl hscale)

theorem jointPrice_f (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (q0 : ℝ) (3/4))
    (w P s M : ℝ) :
    (jointPrice B₀ L₀ c₀ hL q hq).f w P s M =
      max (q w * deletionNeed B₀ L₀ c₀ P s M) (highSup (q w) P s M) := rfl

theorem jointPrice_lip (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (q0 : ℝ) (3/4)) :
    (jointPrice B₀ L₀ c₀ hL q hq).lip = needLip B₀ L₀ c₀ := rfl

theorem count_decrease {ν δ₁ δ₂ : ℝ}
    (hν : ν ∈ Set.Icc (q0:ℝ) (3/4))
    (hδ₁ : δ₁ ∈ Set.Icc (1/2:ℝ) ν) (hδ₂ : δ₂ ∈ Set.Icc (1/2:ℝ) ν)
    (hδ : δ₁ ≤ δ₂) :
    jointCountExponent ν δ₂ ≤ jointCountExponent ν δ₁-(3/25:ℝ)*(δ₂-δ₁) := by
  have h₁ := AdaptivePrice.count_den_pos hν.2 hδ₁.2
  have h₂ := AdaptivePrice.count_den_pos hν.2 hδ₂.2
  have hb : 0 ≤ 5*(1-ν) := by linarith [hν.2]
  have hu₁ : 3-ν-2*δ₁ ≤ 5*(1-ν) := by linarith [hν.2,hδ₁.1]
  have hu₂ : 3-ν-2*δ₂ ≤ 5*(1-ν) := by linarith [hν.2,hδ₂.1]
  have hprod := mul_le_mul hu₁ hu₂ h₂.le hb
  have hg : 0 ≤ (3/25:ℝ)*(δ₂-δ₁) := by positivity
  have hpaid := mul_le_mul_of_nonneg_right hprod hg
  have hi : (3/25:ℝ)*(δ₂-δ₁) ≤
      3*(1-ν)^2*(δ₂-δ₁)/((3-ν-2*δ₁)*(3-ν-2*δ₂)) := by
    apply (le_div_iff₀ (mul_pos h₁ h₂)).mpr
    nlinarith
  rw [← AdaptivePrice.count_difference hν.2 hδ₁.2 hδ₂.2] at hi
  linarith



theorem k_le_nu {ν : ℝ} (hν : ν ∈ Icc q0 (3/4)) : k ν ≤ ν := by
  have hn : 0 ≤ ν := q0_pos.le.trans hν.1
  have hp : 0 ≤ 5-6*ν := by linarith [hν.2]
  rw [k,div_le_iff₀ (k_den_pos hν)]
  nlinarith [mul_nonneg hn hp]

theorem k_difference {x y : ℝ} (hx : x ∈ Icc q0 (3/4)) (hy : y ∈ Icc q0 (3/4)) :
    k y-k x=(y-x)*(150/((15-6*x)*(15-6*y))) := by
  simpa only [one_sub_rhoOf,k] using one_sub_rhoOf_sub x y (k_den_pos hx).ne' (k_den_pos hy).ne'

theorem k_slope_flat {x y : ℝ} (hx : x ∈ Icc q0 (3/4)) (hy : y ∈ Icc q0 (3/4)) :
    (25/24:ℝ) ≤ 150/((15-6*x)*(15-6*y)) := by
  have hd₁ := k_den_pos hx
  have hd₂ := k_den_pos hy
  apply (le_div_iff₀ (mul_pos hd₁ hd₂)).2
  have ha : 15-6*x ≤ (12:ℝ) := by dsimp [q0] at hx; linarith [hx.1]
  have hb : 15-6*y ≤ (12:ℝ) := by dsimp [q0] at hy; linarith [hy.1]
  nlinarith [mul_le_mul ha hb hd₂.le (by norm_num : (0:ℝ) ≤ 12)]

theorem k_slope_curved {x y : ℝ} (hx : x ∈ Icc (7/10:ℝ) (3/4)) (hy : y ∈ Icc (7/10:ℝ) (3/4)) :
    (625/486:ℝ) ≤ 150/((15-6*x)*(15-6*y)) := by
  have hd₁ : 0 < 15-6*x := by linarith [hx.2]
  have hd₂ : 0 < 15-6*y := by linarith [hy.2]
  apply (le_div_iff₀ (mul_pos hd₁ hd₂)).2
  have ha : 15-6*x ≤ (54/5:ℝ) := by linarith [hx.1]
  have hb : 15-6*y ≤ (54/5:ℝ) := by linarith [hy.1]
  nlinarith [mul_le_mul ha hb hd₂.le (by norm_num : (0:ℝ) ≤ 54/5)]

theorem count_above_slope {ν δ : ℝ} (hν : ν ∈ Icc q0 (3/4))
    (hδ : δ ∈ Icc (slope ν) ν) :
    jointCountExponent ν δ ≤ (1-k ν)-1/250-(3/25:ℝ)*(δ-slope ν) := by
  have hs := slope_bounds hν
  have hκ : slope ν ∈ Icc (1/2:ℝ) ν := ⟨by dsimp [amplitudeFloor] at hs; linarith,hs.2⟩
  have hd : δ ∈ Icc (1/2:ℝ) ν := ⟨hκ.1.trans hδ.1,hδ.2⟩
  have hm := count_decrease hν hκ hd hδ.1
  have hb := count_at_slope hν
  dsimp [reserve] at hb
  linarith

theorem joint_energy_small_cap_high {ν δ P s M : ℝ} (hν : ν ∈ Icc q0 (3/4))
    (hδ : δ ∈ Icc (slope ν) ν) (hM : 0 ≤ M) (hs : s ≤ M/10) :
    jointCountExponent ν δ*M+ν*P+δ*s ≤ (1-k ν)*M+ν*P+slope ν*s-M/250 := by
  have hc := mul_le_mul_of_nonneg_right (count_above_slope hν hδ) hM
  have hg : 0 ≤ δ-slope ν := sub_nonneg.mpr hδ.1
  have hp := mul_nonneg hg (show 0 ≤ (3/25:ℝ)*M-s by linarith)
  nlinarith

theorem joint_energy_small_cap {ν δ P s M : ℝ} (hν : ν ∈ Icc q0 (3/4))
    (hδ : δ ∈ Icc (1001/2000:ℝ) ν) (hM : 0 ≤ M) (hs0 : 0 ≤ s) (hs : s ≤ M/10) :
    min (1-k ν) (jointCountExponent ν δ)*M+ν*P+δ*s ≤ M+g ν P s M := by
  have he : M+g ν P s M=(1-k ν)*M+ν*P+slope ν*s := by
    rw [g,max_eq_right (by linarith : s-M/10 ≤ 0),mul_zero]
    ring
  rw [he]
  by_cases hκ : δ ≤ slope ν
  · have hm := mul_le_mul_of_nonneg_right (min_le_left (1-k ν) (jointCountExponent ν δ)) hM
    have hslot := mul_le_mul_of_nonneg_right hκ hs0
    linarith
  · have hb := joint_energy_small_cap_high hν ⟨le_of_not_ge hκ,hδ.2⟩ hM hs (P:=P)
    have hm := mul_le_mul_of_nonneg_right (min_le_right (1-k ν) (jointCountExponent ν δ)) hM
    linarith

theorem joint_energy_le_g {ν δ P s M : ℝ} (hν : ν ∈ Icc q0 (3/4))
    (hδ : δ ∈ Icc (1001/2000:ℝ) ν) (hM : 0 ≤ M) (hs0 : 0 ≤ s) :
    min (1-k ν) (jointCountExponent ν δ)*M+ν*P+δ*s ≤ M+g ν P s M := by
  by_cases hs : s ≤ M/10
  · exact joint_energy_small_cap hν hδ hM hs0 hs
  · have hb := joint_energy_small_cap hν hδ hM (by linarith : 0 ≤ M/10) le_rfl (P:=P)
    have hp := mul_le_mul_of_nonneg_right hδ.2 (show 0 ≤ s-M/10 by linarith)
    have he : g ν P (M/10) M=ν*P-k ν*M+slope ν*(M/10) := by simp [g]
    rw [he] at hb
    rw [g,max_eq_left (by linarith : 0 ≤ s-M/10)]
    nlinarith

theorem zero_energy_le_g_of_delta_le {ν δ P s M : ℝ} (hν : ν ∈ Icc q0 (3/4))
    (hδ : δ ≤ slope ν) (hs : 0 ≤ s) :
    (1-k ν)*M+ν*P+δ*s ≤ M+g ν P s M := by
  have hp := mul_le_mul_of_nonneg_right hδ hs
  have he := mul_nonneg (extensionCoeff_nonneg hν) (le_max_right (s-M/10) 0)
  unfold g
  nlinarith

theorem zero_energy_le_g_of_delta_le_cutoff {ν δ P s M : ℝ} (hν : ν ∈ Icc q0 (3/4))
    (hδ : δ ≤ amplitudeCutoff) (hs : 0 ≤ s) :
    (1-k ν)*M+ν*P+δ*s ≤ M+g ν P s M := by
  have hκ := (slope_bounds hν).1
  have hd : δ ≤ slope ν := by dsimp [amplitudeFloor,amplitudeCutoff] at hδ hκ; linarith
  exact zero_energy_le_g_of_delta_le hν hd hs

theorem joint_energy_le_highSup {q ν δ P s M : ℝ}
    (hq : q ∈ Icc q0 (3/4)) (hν : ν ∈ Icc q (3/4))
    (hδ : δ ∈ Icc (1001/2000:ℝ) ν) (hM : 0 ≤ M) (hs : 0 ≤ s) :
    min (1-k ν) (jointCountExponent ν δ)*M+ν*P+δ*s ≤ M+highSup q P s M :=
  (joint_energy_le_g ⟨hq.1.trans hν.1,hν.2⟩ hδ hM hs).trans
    (add_le_add le_rfl (le_highSup hq.1 hν.1 hν.2 P s M))


theorem slope_sub_le {x y : ℝ} (hx : x ∈ Icc q0 (3/4)) (hy : y ∈ Icc q0 (3/4))
    (hxy : x ≤ y) : slope y-slope x ≤ 3*(y-x) := by
  have hh := slope_lipschitz hx hy
  rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at hh
  exact (le_abs_self _).trans hh

theorem zero_energy_le_highSup {q ν δ P s M : ℝ}
    (hq : q ∈ Icc q0 (3/4)) (hν : ν ∈ Icc q (3/4))
    (hδ : δ ≤ amplitudeCutoff) (hs : 0 ≤ s) :
    (1-k ν)*M+ν*P+δ*s ≤ M+highSup q P s M :=
  (zero_energy_le_g_of_delta_le_cutoff ⟨hq.1.trans hν.1,hν.2⟩ hδ hs).trans
    (add_le_add le_rfl (le_highSup hq.1 hν.1 hν.2 P s M))

/-- Both HIGH pointwise estimates retain the slot exponent min(δ,ν).
The SC count at δ=.75 therefore pays the whole top amplitude class. -/
theorem jointRate_energy {q ν δ P s M : ℝ}
    (hq : q ∈ Icc q0 (3/4)) (hν : ν ∈ Icc q (3/4))
    (hδ : δ ∈ Icc (1001/2000:ℝ) (3/4)) (hM : 0 ≤ M) (hs : 0 ≤ s) :
    AdaptivePrice.jointRate ν δ*M+ν*P+min δ ν*s ≤ M+highSup q P s M := by
  have hνg : ν ∈ Icc q0 (3/4) := ⟨hq.1.trans hν.1,hν.2⟩
  unfold AdaptivePrice.jointRate
  split_ifs with h
  · rw [min_eq_left h]
    exact joint_energy_le_highSup hq hν ⟨hδ.1,h⟩ hM hs
  · have hvd : ν ≤ δ := le_of_not_ge h
    rw [min_eq_right hvd]
    have he : jointCountExponent ν ν=1-ν := by
      unfold jointCountExponent witnessDen
      have hd : 3*(1-ν) ≠ 0 := by nlinarith [hν.2]
      have hh : 3*(1-ν)+2*(ν-ν)=3*(1-ν) := by ring
      rw [hh]
      field_simp
    have hk := k_le_nu hνg
    have hb := joint_energy_le_highSup hq hν
      (show ν ∈ Icc (1001/2000:ℝ) ν from ⟨by dsimp [q0] at hνg; linarith [hνg.1],le_rfl⟩) hM hs (P:=P)
    rw [he,min_eq_right (by linarith)] at hb
    have hr := mul_le_mul_of_nonneg_right
      ((min_le_right (1-k ν) (1-δ)).trans (show 1-δ ≤ 1-ν by linarith)) hM
    exact le_trans (by change min (1-k ν) (1-δ)*M+ν*P+ν*s ≤ _; linarith) hb

theorem rebate_negative_at_lower : k q0-slope q0 < 0 := by
  rw [slope_flat (show q0 ∈ Icc q0 (7/10) from ⟨le_rfl,by norm_num [q0]⟩)]
  norm_num [k,q0,amplitudeFloor]

theorem global_M_lipschitz_lt_three_quarters : (1034923/1400000:ℝ) < 3/4 := by norm_num

end
end Qrh.JointDetector.PointwisePrice

#print axioms Qrh.JointDetector.PointwisePrice.curve_count_identity
#print axioms Qrh.JointDetector.PointwisePrice.slope_lipschitz
#print axioms Qrh.JointDetector.PointwisePrice.slope_flat
#print axioms Qrh.JointDetector.PointwisePrice.jointPrice
#print axioms Qrh.JointDetector.PointwisePrice.jointRate_energy
