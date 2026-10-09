import QRH.Certificate

namespace QRH
noncomputable section

/-- Equation `eq:E`, before choosing a row-count exponent. -/
def exponent (d δ q R : ℝ) : ℝ :=
  (1 + δ) / 2 - tightTheta + h * (17 / 50 - 1 / 6) -
    (1 + δ) / 2 * ly - ell / 2 + q * ell + d * (R + δ / 2 - 17 / 50)

def adaptiveCount (δ x : ℝ) : ℝ :=
  1 - δ + (5 / 6 - δ) * δ * Certificate.P x / (2 * Certificate.J δ x)

theorem endpoint_is_manuscript (δ x : ℝ) :
    exponent h δ (x * δ) (adaptiveCount δ x) = Certificate.E δ x := by
  unfold exponent adaptiveCount Certificate.E
  ring

theorem exponent_mono_amplitude {d δ q R : ℝ} (hq : q ≤ δ / 2) :
    exponent d δ q R ≤ exponent d δ (δ / 2) R := by
  have hell : 0 ≤ ell := by norm_num [ell, tightTheta]
  have hh := mul_le_mul_of_nonneg_right hq hell
  unfold exponent
  linarith

theorem floor_saving : exponent h (1 / 50) (1 / 100) 1 < -(1 / 200 : ℝ) := by
  norm_num [exponent, h, lx, ly, M, b, ell, tightTheta]



theorem large_formula (δ : ℝ) :
    exponent h δ (δ / 2) (1 - δ) = (-6 * b * δ + 2 * b + 15 * ell - 3) / 12 := by
  unfold exponent h lx ly M ell
  ring



theorem large_saving {δ q : ℝ} (hd : (5 / 6 : ℝ) ≤ δ) (hq : q ≤ δ / 2) :
    exponent h δ q (1 - δ) < -(7 / 100 : ℝ) := by
  apply lt_of_le_of_lt (exponent_mono_amplitude hq)
  rw [large_formula]
  norm_num [b, ell, tightTheta]
  linarith





end
end QRH
