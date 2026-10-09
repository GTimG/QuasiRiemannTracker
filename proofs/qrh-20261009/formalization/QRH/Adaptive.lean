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
  have hc0 : 0 ≤ c := by norm_num [c, kappa0, theta]
  have hc1 : c ≤ (6 / 13 : ℝ) := by norm_num [c, kappa0, theta]
  have hcx0 : 0 ≤ c * x := mul_nonneg hc0 hx0
  have hcx1 : c * x ≤ (3 / 13 : ℝ) := by
    calc c * x ≤ (6 / 13 : ℝ) * x := mul_le_mul_of_nonneg_right hc1 hx0
         _ ≤ 3 / 13 := by linarith
  have hp : (10 / 13 : ℝ) ≤ P x := by
    have hprod := mul_le_mul (show (20 / 13 : ℝ) ≤ 2 - 2 * c * x by linarith)
      (show (1 / 2 : ℝ) ≤ 1 - x by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (show 0 ≤ 2 - 2 * c * x by linarith)
    dsimp [P]
    nlinarith [hprod]
  refine ⟨hp, ?_, ?_⟩
  · have hh := mul_nonneg hx0 (show 0 ≤ 1 - 2 * c * x by linarith)
    dsimp [P, D]
    nlinarith [hh]
  · dsimp [D]
    nlinarith

theorem witness_range {δ x : ℝ} (hd0 : 0 ≤ δ) (hd1 : δ ≤ 5 / 6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    1 ≤ witness δ x ∧ witness δ x ≤ 3 / 2 := by
  have hj := denominator_bounds hd0 hd1 hx0 hx1
  have hp := DP_bounds hx0 hx1
  have hjpos : 0 < 2 * J δ x := by linarith [hj.1]
  have hp0 : 0 ≤ P x := by linarith [hp.1]
  have hdpos : 0 ≤ D x := hp0.trans hp.2.1
  have hsmall := mul_nonneg (show 0 ≤ 5 / 6 - δ by linarith) hdpos
  constructor
  · unfold witness
    have := div_nonneg (mul_nonneg hd0 hp0) hjpos.le
    linarith
  · have hh : δ * P x / (2 * J δ x) ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hjpos).mpr
      dsimp [J] at *
      linarith
    unfold witness
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
  constructor
  · field_simp
    ring
  · field_simp
    unfold J
    ring

end
end QRH.Certificate
