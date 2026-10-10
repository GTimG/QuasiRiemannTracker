import QRH.OtherRanges

namespace QRH.Certificate
noncomputable section
open QRH

def witness (δ x : ℝ) : ℝ := 1 + δ * P x / (2 * J δ x)
def inverseCount (δ x r : ℝ) : ℝ := 1 - δ * (x + (1 - x) * r)
def plainCount (δ x t r : ℝ) : ℝ := 1 - δ * (c * x + (2 - 2 * c * x) * (t - r))
def crossing (x t : ℝ) : ℝ := ((2 - 2 * c * x) * t + (c - 1) * x) / D x

theorem DP_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    (10 / 13 : ℝ) ≤ P x ∧ P x ≤ D x ∧ D x ≤ 3 := by
  have hc0 := c_bounds.1
  have hc1 := c_bounds.2
  have hcg := mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ 1 / 2 - x by linarith)
  have ha : 2 - c ≤ 2 - 2 * c * x := by nlinarith
  have hb : (1 / 2 : ℝ) ≤ 1 - x := by linarith
  have hp := mul_le_mul ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (show 0 ≤ 2 - 2 * c * x by nlinarith)
  have hcx : 0 ≤ 1 - 2 * c * x := by nlinarith
  have hpx := mul_nonneg hx0 hcx
  have hdx := mul_nonneg hx0 (show 0 ≤ 1 + 2 * c by linarith)
  dsimp [P, D]
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem witness_range {δ x : ℝ} (hd0 : 0 ≤ δ) (hd1 : δ ≤ 5 / 6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    1 ≤ witness δ x ∧ witness δ x ≤ 3 / 2 := by
  have hj := denominator_bounds hd0 hd1 hx0 hx1
  have hp := DP_bounds hx0 hx1
  have hjpos : 0 < 2 * J δ x := by linarith [hj.1]
  have hp0 : 0 ≤ P x := by linarith [hp.1]
  have hsmall := mul_nonneg (show 0 ≤ 5 / 6 - δ by linarith) (hp0.trans hp.2.1)
  unfold witness
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  · rw [← le_sub_iff_add_le', div_le_iff₀ hjpos]
    dsimp [J] at *
    linarith



theorem balanced_counts {δ x : ℝ} (hj : J δ x ≠ 0) (hd : D x ≠ 0) :
    (1 - δ + (5 / 6 - δ) * (witness δ x - 1) = adaptiveCount δ x) ∧
    (1 - δ + δ * P x / D x * (3 / 2 - witness δ x) = adaptiveCount δ x) := by
  unfold witness adaptiveCount
  constructor <;> field_simp <;> unfold J <;> ring

end
end QRH.Certificate
