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
  norm_num [P, D, c, kappa0, theta]
  refine ⟨?_, ?_, hx0⟩ <;>
    nlinarith [sq_nonneg (x - 1 / 2), mul_nonneg hx0 (sub_nonneg.mpr hx1)]

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

theorem crossing_identity {δ x t : ℝ} (hd : D x ≠ 0) :
    inverseCount δ x (crossing x t) = plainCount δ x t (crossing x t) := by
  unfold inverseCount plainCount crossing
  field_simp
  unfold D
  ring

theorem balanced_counts {δ x : ℝ} (hj : J δ x ≠ 0) (hd : D x ≠ 0) :
    (1 - δ + (5 / 6 - δ) * (witness δ x - 1) = adaptiveCount δ x) ∧
    (1 - δ + δ * P x / D x * (3 / 2 - witness δ x) = adaptiveCount δ x) := by
  unfold witness adaptiveCount
  constructor <;> field_simp <;> unfold J <;> ring

end
end QRH.Certificate
