import WeightedQRH.HighRows.CountIdentity
import OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm

namespace WeightedQRH
noncomputable section

/-- Exact scale of the original central Mellin cube at the new physical geometry. -/
def centralScale (a e : ℝ) : ℝ := (1081 / 2000) * a - 7503 / 12500 + (13243 / 1000) * e

theorem physical_scale_identity (Z a e : ℝ) (hZ : 0 < Z) :
    (Z^(747/2000:ℝ))^(4/25:ℝ)*
      Z^(a+16*e-(33/50:ℝ))*(Z^(919/2000:ℝ))^(-a-6*e) =
      Z^(centralScale a e) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ, ←Real.rpow_add hZ]
  congr 1
  unfold centralScale
  ring

/-- The branches that retain the original pointwise numerator estimate. -/
def OriginalBranch (d a : ℝ) : Prop :=
  d ≤ h + rowExtension ∧ (2 * a - 1 ≤ 1 / 3 ∨ d ≤ 1 / 2)

theorem original_branch_exponent {d a q : ℝ}
    (hd0 : 0 ≤ d) (ha0 : 51 / 100 < a) (ha1 : a ≤ 7 / 8)
    (hq0 : 0 ≤ q) (hq1 : q ≤ (2 * a - 1) / 2)
    (hbranch : OriginalBranch d a) :
    genericOldExponent d (2 * a - 1) q (rowCount (2 * a - 1) (q / (2 * a - 1))) ≤
      -(1 / 20000 : ℝ) := by
  have hδ0 : 0 < 2 * a - 1 := by linarith
  have hδ1 : 2 * a - 1 ≤ 3 / 4 := by linarith
  have hx0 : 0 ≤ q / (2 * a - 1) := div_nonneg hq0 hδ0.le
  have hx1 : q / (2 * a - 1) ≤ 1 / 2 := (div_le_iff₀ hδ0).mpr (by linarith)
  have hq : (2 * a - 1) * (q / (2 * a - 1)) = q := mul_div_cancel₀ q hδ0.ne'
  rcases hbranch with ⟨hd, hb | hb⟩
  · have he := old_extended_bound hd hδ0.le hb hx0 hx1
    simpa only [oldExponent, hq] using he
  · have hr := rowCount_density_bound hδ0.le hδ1 hx0 hx1
    have hm : genericOldExponent d (2 * a - 1) q (rowCount (2 * a - 1) (q / (2 * a - 1))) ≤
        genericOldExponent d (2 * a - 1) ((2 * a - 1) / 2) (76 / 75 - 2 * (2 * a - 1) / 3) := by
      have hp1 := mul_nonneg (sub_nonneg.mpr hq1) ell_pos.le
      have hp2 := mul_nonneg hd0 (show 0 ≤ 76 / 75 - 2 * (2 * a - 1) / 3 -
        rowCount (2 * a - 1) (q / (2 * a - 1)) by linarith)
      unfold genericOldExponent
      nlinarith
    have he := intermediate_row_bound hb (by linarith : 1 / 50 ≤ 2 * a - 1) hδ1
    linarith

theorem central_exponent_identity (d v a q countLoss rowLoss outerLoss : ℝ) :
    centralScale a 0 + d * (rowCount (2 * a - 1) (q / (2 * a - 1)) + countLoss) +
      v * (a - 1 / 2 - 17 / 50 + rowLoss) + outerLoss - 167 / 6250 + q * 167 / 1000 =
    genericOldExponent d (2 * a - 1) q (rowCount (2 * a - 1) (q / (2 * a - 1))) + signal theta +
      d * countLoss + v * rowLoss + outerLoss + (d - v) * (17 / 50 - (a - 1 / 2)) := by
  unfold centralScale genericOldExponent signal theta b h ly ell
  ring

theorem central_class_saving {d v a q countLoss rowLoss outerLoss μ : ℝ}
    (hd0 : 0 ≤ d) (hv0 : 0 ≤ v) (hvd : v ≤ d) (hdv : d - v ≤ μ)
    (ha0 : 51 / 100 < a) (ha1 : a ≤ 7 / 8)
    (hq0 : 0 ≤ q) (hq1 : q ≤ (2 * a - 1) / 2)
    (hbranch : OriginalBranch d a) (hc : 0 ≤ countLoss) (hr : 0 ≤ rowLoss)
    (hbudget : countLoss + rowLoss + outerLoss + μ ≤ 1 / 40000) :
    centralScale a 0 + d * (rowCount (2 * a - 1) (q / (2 * a - 1)) + countLoss) +
      v * (a - 1 / 2 - 17 / 50 + rowLoss) + outerLoss - 167 / 6250 + q * 167 / 1000 ≤
      signal theta - 1 / 40000 := by
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
    (hd0 : 0 ≤ d) (hv0 : 0 ≤ v) (hvd : v ≤ d) (hdv : d - v ≤ μ)
    (ha0 : 51 / 100 < a) (ha1 : a ≤ 7 / 8)
    (hq0 : 0 ≤ q) (hq1 : q ≤ (2 * a - 1) / 2)
    (hbranch : OriginalBranch d a)
    (hε : 0 ≤ ε) (hεm : 0 ≤ εm) (hR : 0 ≤ R) (hν : 0 ≤ ν)
    (he : 0 ≤ e) (heps : 0 ≤ eps)
    (hbudget : (159 * ε + εm + R + 7 * ν) + (12 * e + eps * (N + 8)) +
      (logCost + heightCost + momentCost + loss + mesh * 167 / 1000 + (13243 / 1000) * e) + μ ≤ 1 / 40000) :
    logCost + heightCost + momentCost +
      d * OAI.SevenEighths.ProbeHighRowFamily.adaptiveRowExponent (2*a-1) q 0 ε εm R ν +
      v * (a-1/2+12*e+eps*(N+8)-17/50) + loss - 167/6250 + q*167/1000 + mesh*167/1000 ≤
      signal theta - 1 / 40000 - centralScale a e := by
  rw [adaptive_count_identity (by linarith) (by linarith) hq0 hq1]
  have hh := central_class_saving hd0 hv0 hvd hdv ha0 ha1 hq0 hq1 hbranch
    (show 0 ≤ 159 * ε + εm + R + 7 * ν by positivity)
    (show 0 ≤ 12 * e + eps * (N + 8) by positivity) hbudget
  unfold centralScale at *
  linarith


def floorSourceExponent (v : ℝ) : ℝ := centralScale (51/100) 0 + v * (67/100) - 501/20000

def floorRealLoss (N : ℕ) (v e eps loss mesh : ℝ) : ℝ :=
  (13243/1000)*e + v*(12*e+eps*(N+8)) + loss + mesh*167/1000

theorem floor_source_margin {v : ℝ} (hv : v ≤ h + rowExtension) :
    floorSourceExponent v ≤ signal theta - 1/100 := by
  norm_num [floorSourceExponent, centralScale, signal, theta, b, h, rowExtension] at *
  linarith

theorem floor_loss_bound (N : ℕ) {v e eps loss mesh : ℝ}
    (hv : v ≤ 1) (he : 0 ≤ e) (heps : 0 ≤ eps) :
    floorRealLoss N v e eps loss mesh ≤ 26*e+(N+8)*eps+loss+mesh*167/1000 := by
  have hp := mul_le_mul_of_nonneg_right hv (show 0 ≤ 12*e+eps*(N+8) by positivity)
  unfold floorRealLoss
  nlinarith

end
end WeightedQRH
