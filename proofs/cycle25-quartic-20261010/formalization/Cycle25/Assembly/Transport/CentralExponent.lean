import Cycle25.Assembly.Transport.EasyExponent
import Cycle25.Assembly.Transport.FloorExponent
noncomputable section
namespace Cycle25.Transport
lemma adaptive_count_identity {delta q epsilon em R nu : ℝ} (hd : 0<delta) (hd1 : delta≤3/4) (_hq : 0≤q) (_hq1 : q≤delta/2) :
    OAI.SevenEighths.ProbeHighRowFamily.adaptiveRowExponent delta q 0 epsilon em R nu =
    oldCount delta (q/delta)+(159*epsilon+em+R+7*nu) := by
  simp only [OAI.SevenEighths.ProbeHighRowFamily.adaptiveRowExponent,ite_eq_left (show delta≤5/6 by linarith),zero_div,add_zero]
  unfold oldCount
  ring
theorem central_exponent_identity (d v a q countLoss rowLoss outerLoss : ℝ) :
    centralScale a 0 + d * (oldCount (2 * a - 1) (q / (2 * a - 1)) + countLoss) +
      v * (a - 1 / 2 - 17 / 50 + rowLoss) + outerLoss - 4*ell/25 + q * ell =
    genericOldExponent d (2 * a - 1) q (oldCount (2 * a - 1) (q / (2 * a - 1))) + signal theta +
      d * countLoss + v * rowLoss + outerLoss + (d - v) * (17 / 50 - (a - 1 / 2)) := by
  unfold centralScale genericOldExponent Cycle25.signal Cycle25.b
  rw [Cycle25.y_endpoint,Cycle25.row_endpoint]
  ring

theorem central_class_saving {d v a q countLoss rowLoss outerLoss μ : ℝ}
    (hd0 : 0 ≤ d) (_hv0 : 0 ≤ v) (hvd : v ≤ d) (hdv : d - v ≤ μ)
    (ha0 : 51 / 100 < a) (ha1 : a ≤ 7 / 8)
    (hq0 : 0 ≤ q) (hq1 : q ≤ (2 * a - 1) / 2)
    (hbranch : OriginalBranch d a) (hc : 0 ≤ countLoss) (hr : 0 ≤ rowLoss)
    (hbudget : countLoss + rowLoss + outerLoss + μ ≤ 1 / 4000) :
    centralScale a 0 + d * (oldCount (2 * a - 1) (q / (2 * a - 1)) + countLoss) +
      v * (a - 1 / 2 - 17 / 50 + rowLoss) + outerLoss - 4*ell/25 + q * ell ≤
      signal theta - 1 / 4000 := by
  have he := original_branch_exponent hd0 ha0 ha1 hq0 hq1 hbranch
  have hd1 : d ≤ 1 := hbranch.1.trans extended_h_lt_one.le
  have hv1 : v ≤ 1 := hvd.trans hd1
  have hc' := mul_le_mul_of_nonneg_right hd1 hc
  have hr' := mul_le_mul_of_nonneg_right hv1 hr
  have hp := mul_nonneg (sub_nonneg.mpr hvd) (show 0 ≤ a - 1 / 2 by linarith)
  have hμ : (d - v) * (17 / 50 - (a - 1 / 2)) ≤ μ := by nlinarith
  rw [central_exponent_identity]
  nlinarith

/-- Actual count and physical-loss bookkeeping used by the original central cube. -/
theorem actual_central_class_saving (N : ℕ) {d v a q ε εm R ν e eps loss mesh
    logCost heightCost momentCost μ : ℝ}
    (hd0 : 0 ≤ d) (_hv0 : 0 ≤ v) (hvd : v ≤ d) (hdv : d - v ≤ μ)
    (ha0 : 51 / 100 < a) (ha1 : a ≤ 7 / 8)
    (hq0 : 0 ≤ q) (hq1 : q ≤ (2 * a - 1) / 2)
    (hbranch : OriginalBranch d a)
    (hε : 0 ≤ ε) (hεm : 0 ≤ εm) (hR : 0 ≤ R) (hν : 0 ≤ ν)
    (he : 0 ≤ e) (heps : 0 ≤ eps)
    (hbudget : (159 * ε + εm + R + 7 * ν) + (12 * e + eps * (N + 8)) +
      (logCost + heightCost + momentCost + loss + mesh * ell + (16-6*ly) * e) + μ ≤ 1 / 4000) :
    logCost + heightCost + momentCost +
      d * OAI.SevenEighths.ProbeHighRowFamily.adaptiveRowExponent (2*a-1) q 0 ε εm R ν +
      v * (a-1/2+12*e+eps*(N+8)-17/50) + loss - 4*ell/25 + q*ell + mesh*ell ≤
      signal theta - 1 / 4000 - centralScale a e := by
  rw [adaptive_count_identity (by linarith) (by linarith) hq0 hq1]
  have hh := central_class_saving hd0 _hv0 hvd hdv ha0 ha1 hq0 hq1 hbranch
    (show 0 ≤ 159 * ε + εm + R + 7 * ν by positivity)
    (show 0 ≤ 12 * e + eps * (N + 8) by positivity) hbudget
  unfold centralScale at *
  nlinarith


end Cycle25.Transport
