import Mathlib

/-!
Exact real parameters for the weighted physical numerator proof.
No analytic theorem or QRH conclusion is assumed in this module.
-/

namespace Cycle25.Weighted

noncomputable section

def theta : ℝ := 10499 / 12000
def ell : ℝ := 167 / 1000
def b : ℝ := 43 / 500
def lx : ℝ := 747 / 2000
def ly : ℝ := 919 / 2000
def h : ℝ := 1587 / 2000
def kappa : ℝ := 3 / 4
def endpointMargin : ℝ := 1 / 10000
def rowExtension : ℝ := 1 / 1000000
def publicBenchmark : ℝ := 874957019420098946128604623 / 10^27
def signal (s : ℝ) : ℝ := s - (4 + b) / 6

theorem theta_eq : theta = (11 : ℝ) / 12 - ell / 4 := by
  norm_num [theta, ell]

theorem theta_pos : 0 < theta := by norm_num [theta]
theorem theta_lt_seven_eighths : theta < (7 : ℝ) / 8 := by norm_num [theta]
theorem theta_lt_public : theta < publicBenchmark := by
  norm_num [theta, publicBenchmark]
theorem theta_gt_half : (1 : ℝ) / 2 < theta := by norm_num [theta]
theorem theta_lt_one : theta < 1 := by norm_num [theta]
theorem kappa_admissible : (1 + kappa) / 2 = (7 : ℝ) / 8 := by
  norm_num [kappa]
theorem endpointMargin_pos : 0 < endpointMargin := by norm_num [endpointMargin]
theorem rowExtension_pos : 0 < rowExtension := by norm_num [rowExtension]
theorem rowExtension_cost : 2 * rowExtension < endpointMargin / 2 := by
  norm_num [rowExtension, endpointMargin]

theorem length_sum : lx + ly = 1 - ell := by norm_num [lx, ly, ell]
theorem length_difference : ly - lx = b := by norm_num [lx, ly, b]
theorem row_endpoint : h = 1 - lx + ell := by norm_num [h, lx, ell]
theorem signal_low : signal theta = lx / 2 + b / 12 := by
  norm_num [signal, theta, lx, b]
theorem signal_slope (s t : ℝ) : signal s - signal t = s - t := by
  simp only [signal]; ring

theorem b_pos : 0 < b := by norm_num [b]
theorem ell_pos : 0 < ell := by norm_num [ell]
theorem ell_lt_one_fifth : ell < (1 : ℝ) / 5 := by norm_num [ell]
theorem x_rescaled_pos : 0 < lx - ell := by norm_num [lx, ell]
theorem y_rescaled_pos : 0 < ly - ell := by norm_num [ly, ell]
theorem row_rescaled_pos : 0 < 1 - 3 * ell := by norm_num [ell]
theorem gram_domination : 0 < ly - ell - (11 : ℝ) / 6 * b := by
  norm_num [ly, ell, b]
theorem h_pos : 0 < h := by norm_num [h]
theorem h_gt_half : (1 : ℝ) / 2 < h := by norm_num [h]
theorem h_lt_one : h < 1 := by norm_num [h]
theorem row_count_supply : (7 : ℝ) / 37 < ell / h := by norm_num [ell, h]
theorem row_extension_supply : h < 5 * ell := by norm_num [h, ell]
theorem numerator_short : h < 2 * ly := by norm_num [h, ly]
theorem ly_lt_half : ly < (1 : ℝ) / 2 := by norm_num [ly]
theorem numerator_supply : (2 * ly - (1 : ℝ) / 2) / (6 * kappa) < ell := by
  norm_num [ly, kappa, ell]
theorem extended_row_count_supply : (7 : ℝ) / 37 < ell / (h + rowExtension) := by
  norm_num [ell, h, rowExtension]
theorem extended_numerator_short : h + rowExtension < 2 * ly := by
  norm_num [h, rowExtension, ly]
theorem extended_h_lt_one : h + rowExtension < 1 := by norm_num [h, rowExtension]
theorem extended_row_supply : h + rowExtension < 5 * ell := by
  norm_num [h, rowExtension, ell]

theorem numerator_supply_all {d : ℝ} (hd : (1 : ℝ) / 2 ≤ d) :
    (2 * ly - d) / (6 * kappa) < ell := by
  norm_num [ly, kappa, ell] at *
  linarith

theorem numerator_range {d : ℝ} (hd : (1 : ℝ) / 2 ≤ d) (hdh : d ≤ h) :
    d / 2 < ly ∧ ly < d := by
  norm_num [h, ly] at *
  constructor <;> linarith

theorem low_rescaled_tuple {v : ℝ} (hv : 0 ≤ v) :
    -v + max 0 (5 * ell - 1 + v) / 8 ≤ 0 := by
  have hm : max 0 (5 * ell - 1 + v) ≤ 8 * v := by
    apply max_le
    · linarith
    · norm_num [ell]
      linarith
  linarith

theorem low_rescaled_identity (v : ℝ) :
    (1 - ell - 2 * v) + (ell - v) - 1 = -3 * v := by ring

theorem small_row_margin :
    h * ((17 : ℝ) / 50 - 1 / 6) - ly / 2 + 63 / 5000 < 0 := by
  norm_num [h, ly]
theorem principal_w_margin : 0 < ly / 20 := by norm_num [ly]
theorem principal_z_margin : 0 < h / 600 := by norm_num [h]
theorem euler_tail_capacity_gap : (1 : ℝ) / 4 - 1 / (12 * kappa) = 5 / 36 := by
  norm_num [kappa]

theorem principal_local_exponents :
    -(6 : ℝ) * (33 / 200) ≤ -theta ∧
    4 - 5 * theta - 6 * (33 / 200) ≤ -theta ∧
    1 - (19 : ℝ) / 20 - 6 * (33 / 200) ≤ -theta := by
  norm_num [theta]

theorem principal_euler_defects :
    4 - 6 * theta - 6 * ((33 : ℝ) / 200) < -1 ∧
    1 - theta - (19 : ℝ) / 20 - 6 * (33 / 200) < -1 := by
  norm_num [theta]

/-- The exact nonnegative dual identity for the unchanged low estimates. -/
theorem low_barrier_identity (M ℓ e : ℝ) :
    M / 12 - ℓ / 6 + e / 2 - 1 / 30 =
      (1 / 5 : ℝ) * (e - (1 + 3 * ℓ - 2 * M) / 4) +
      (1 / 60 : ℝ) * (e - (M + ℓ - 1)) + (17 / 60 : ℝ) * e := by ring

/-- A limitation of the stated sufficient low-exponent system, not of zeros. -/
theorem low_barrier {B M ℓ e : ℝ}
    (he : 0 ≤ e)
    (henergy₁ : (1 + 3 * ℓ - 2 * M) / 4 ≤ e)
    (henergy₂ : M + ℓ - 1 ≤ e)
    (hlow : (5 : ℝ) / 6 + M / 12 - ℓ / 6 + e / 2 ≤ B) :
    (13 : ℝ) / 15 ≤ B := by
  linarith

/-- The same scoped barrier before eliminating the Gram exponent g. -/
theorem physical_low_barrier {B xLen yLen ℓ g e : ℝ}
    (hg : (yLen - xLen) / 6 ≤ g)
    (he : 0 ≤ e)
    (henergy₁ : (1 + 3 * ℓ - 2 * (xLen + yLen)) / 4 ≤ e)
    (henergy₂ : xLen + yLen + ℓ - 1 ≤ e)
    (hlow : (5 : ℝ) / 6 + xLen / 6 - ℓ / 6 + g / 2 + e / 2 ≤ B) :
    (13 : ℝ) / 15 ≤ B := by
  apply low_barrier he henergy₁ henergy₂
  linarith

end
end Cycle25.Weighted

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
