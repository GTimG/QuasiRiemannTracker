import QRH.Certificate

namespace QRH
noncomputable section

/-- Equation `eq:E`, before choosing a row-count exponent. -/
def exponent (d δ q R : ℝ) : ℝ :=
  (1 + δ) / 2 - theta + h * (17 / 50 - 1 / 6) -
    (1 + δ) / 2 * ly - ell / 2 + q * ell + d * (R + δ / 2 - 17 / 50)

def adaptiveCount (δ x : ℝ) : ℝ :=
  1 - δ + (5 / 6 - δ) * δ * Certificate.P x / (2 * Certificate.J δ x)

theorem endpoint_is_manuscript (δ x : ℝ) :
    exponent h δ (x * δ) (adaptiveCount δ x) = Certificate.E δ x := by
  unfold exponent adaptiveCount Certificate.E
  ring

theorem exponent_mono_amplitude {d δ q R : ℝ} (hq : q ≤ δ / 2) :
    exponent d δ q R ≤ exponent d δ (δ / 2) R := by
  have hell : 0 ≤ ell := by norm_num [ell, theta]
  have hh := mul_le_mul_of_nonneg_right hq hell
  unfold exponent
  linarith

theorem floor_saving : exponent h (1 / 50) (1 / 100) 1 < -(1 / 200 : ℝ) := by
  norm_num [exponent, h, lx, ly, M, b, ell, theta]

theorem short_formula (δ : ℝ) :
    exponent (1 / 2) δ (δ / 2) (76 / 75 - 2 * δ / 3) =
      (-75 * b * δ - 49 * b + 225 * δ * ell + 50 * δ + 78 * ell - 73) / 300 := by
  unfold exponent h lx ly M ell
  ring

theorem large_formula (δ : ℝ) :
    exponent h δ (δ / 2) (1 - δ) = (-6 * b * δ + 2 * b + 15 * ell - 3) / 12 := by
  unfold exponent h lx ly M ell
  ring

theorem short_saving {δ q : ℝ} (hd : δ ≤ 5 / 6) (hq : q ≤ δ / 2) :
    exponent (1 / 2) δ q (76 / 75 - 2 * δ / 3) < -(1 / 500 : ℝ) := by
  apply lt_of_le_of_lt (exponent_mono_amplitude hq)
  rw [short_formula]
  norm_num [b, ell, theta]
  linarith

theorem large_saving {δ q : ℝ} (hd : (5 / 6 : ℝ) ≤ δ) (hq : q ≤ δ / 2) :
    exponent h δ q (1 - δ) < -(7 / 100 : ℝ) := by
  apply lt_of_le_of_lt (exponent_mono_amplitude hq)
  rw [large_formula]
  norm_num [b, ell, theta]
  linarith

theorem small_row_saving :
    h * (17 / 50 - 1 / 6) - ly / 2 + 2 * (1 / 100) < -(7 / 100 : ℝ) := by
  norm_num [h, lx, ly, M, b, ell, theta]

theorem unbounded_tail_saving :
    (lx / 2 + 1 + ly) + (h + zeta) * (1 + zeta) - zeta * (4 * 100000000000000) + zeta < -(1 : ℝ) := by
  norm_num [h, lx, ly, M, b, ell, theta, zeta]

end
end QRH
