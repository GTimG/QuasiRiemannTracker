/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Mathlib.Tactic

/-!
# Appendix P.4 / Q.1: the admitted paired count

These declarations formalize the literal rational expressions in (P9), their
baseline, monotonicity in the contact enclosures, and clearing by the positive
denominator. Admissibility of an analytic count is deliberately not inferred
from these scalar identities.
-/

namespace QRH.Cycle090

noncomputable section

/-- The complementary density `v = 5/6 - d` from (P9). -/
def pairedV (d : ℝ) : ℝ := 5 / 6 - d

/-- The amplitude coefficient `k` from (P9). -/
def pairedK (p g₁ : ℝ) : ℝ := 1 - p * (1 + 2 * g₁)

/-- The numerator coefficient `U₀` from (P9). -/
def pairedU (p g₀ g₁ : ℝ) : ℝ := 1 - p * (1 + 6 * g₀ - 4 * g₁)

/-- The denominator `J` of the admitted paired count. -/
def pairedJ (d p g₁ : ℝ) : ℝ := 3 * pairedV d + 2 * d * pairedK p g₁

/-- The numerator `N` of the admitted paired count. -/
def pairedN (d p g₀ g₁ : ℝ) : ℝ :=
  pairedJ d p g₁ / 6 + pairedV d * (pairedJ d p g₁ + d * pairedU p g₀ g₁)

/-- The same-zero crossing parameter `t₀` in (P9). -/
def pairedCrossing (d p g₀ g₁ : ℝ) : ℝ :=
  1 + d * pairedU p g₀ g₁ / pairedJ d p g₁

/-- The scalar admitted paired-count exponent `R = N/J`. -/
def pairedCount (d p g₀ g₁ : ℝ) : ℝ := pairedN d p g₀ g₁ / pairedJ d p g₁

/-- The two displayed expressions for `R` in (P9) agree when `J` is nonzero. -/
theorem pairedCount_eq {d p g₀ g₁ : ℝ} (hJ : pairedJ d p g₁ ≠ 0) :
    pairedCount d p g₀ g₁ = 1 / 6 + pairedV d * pairedCrossing d p g₀ g₁ := by
  unfold pairedCount pairedN pairedCrossing
  field_simp [hJ]

/-- The count is the baseline `1-d` plus its explicit rational correction. -/
theorem pairedCount_eq_base_plus {d p g₀ g₁ : ℝ} (hJ : pairedJ d p g₁ ≠ 0) :
    pairedCount d p g₀ g₁ =
      1 - d + pairedV d * (d * pairedU p g₀ g₁ / pairedJ d p g₁) := by
  rw [pairedCount_eq hJ]
  unfold pairedCrossing pairedV
  ring

/-- The admitted sign conditions imply the baseline used for the slope in (Q2). -/
theorem pairedCount_lower {d p g₀ g₁ : ℝ}
    (hd : 0 ≤ d) (hdUpper : d ≤ 5 / 6)
    (hU : 0 ≤ pairedU p g₀ g₁) (hJ : 0 < pairedJ d p g₁) :
    1 - d ≤ pairedCount d p g₀ g₁ := by
  rw [pairedCount_eq_base_plus (ne_of_gt hJ)]
  have hv : 0 ≤ pairedV d := sub_nonneg.mpr hdUpper
  have hcorrection := mul_nonneg hv
    (div_nonneg (mul_nonneg hd hU) (le_of_lt hJ))
  linarith

/-- Increasing `g₀` weakens the paired count, with the original denominator fixed. -/
theorem pairedCount_antitone_g₀ {d p g₀a g₀b g₁ : ℝ}
    (hd : 0 ≤ d) (hdUpper : d ≤ 5 / 6) (hp : 0 ≤ p)
    (hg : g₀a ≤ g₀b) (hJ : 0 < pairedJ d p g₁) :
    pairedCount d p g₀b g₁ ≤ pairedCount d p g₀a g₁ := by
  have hU : pairedU p g₀b g₁ ≤ pairedU p g₀a g₁ := by
    unfold pairedU
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hg)]
  have hv : 0 ≤ pairedV d := sub_nonneg.mpr hdUpper
  have hquot := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hU hd) (le_of_lt hJ)
  have hweighted := mul_le_mul_of_nonneg_left hquot hv
  rw [pairedCount_eq_base_plus (ne_of_gt hJ), pairedCount_eq_base_plus (ne_of_gt hJ)]
  linarith

/-- Exact finite difference in `g₁`, avoiding any differentiability assumption. -/
theorem pairedCount_g₁_difference {d p g₀ g₁a g₁b : ℝ}
    (hJa : pairedJ d p g₁a ≠ 0) (hJb : pairedJ d p g₁b ≠ 0) :
    pairedCount d p g₀ g₁b - pairedCount d p g₀ g₁a =
      (4 * pairedV d * d * p * (g₁b - g₁a) *
        (pairedJ d p g₁a + d * pairedU p g₀ g₁a)) /
      (pairedJ d p g₁a * pairedJ d p g₁b) := by
  rw [pairedCount_eq_base_plus hJb, pairedCount_eq_base_plus hJa]
  field_simp [hJa, hJb]
  unfold pairedJ pairedU pairedK pairedV
  ring

/-- Increasing `g₁` increases the paired count on its positive admitted branch. -/
theorem pairedCount_monotone_g₁ {d p g₀ g₁a g₁b : ℝ}
    (hd : 0 ≤ d) (hdUpper : d ≤ 5 / 6) (hp : 0 ≤ p)
    (hg : g₁a ≤ g₁b) (hUa : 0 ≤ pairedU p g₀ g₁a)
    (hJa : 0 < pairedJ d p g₁a) (hJb : 0 < pairedJ d p g₁b) :
    pairedCount d p g₀ g₁a ≤ pairedCount d p g₀ g₁b := by
  have hv : 0 ≤ pairedV d := sub_nonneg.mpr hdUpper
  have hsum : 0 ≤ pairedJ d p g₁a + d * pairedU p g₀ g₁a :=
    add_nonneg (le_of_lt hJa) (mul_nonneg hd hUa)
  have hnum : 0 ≤ 4 * pairedV d * d * p * (g₁b - g₁a) *
      (pairedJ d p g₁a + d * pairedU p g₀ g₁a) := by
    positivity
  have hdiff : 0 ≤ pairedCount d p g₀ g₁b - pairedCount d p g₀ g₁a := by
    rw [pairedCount_g₁_difference (ne_of_gt hJa) (ne_of_gt hJb)]
    exact div_nonneg hnum (le_of_lt (mul_pos hJa hJb))
  linarith

/-- Clearing the positive paired denominator preserves the exact top return margin. -/
theorem pairedCount_clear_margin {d p g₀ g₁ target base h : ℝ}
    (hJ : pairedJ d p g₁ ≠ 0) :
    (target - base) * pairedJ d p g₁ - 3 * h * pairedN d p g₀ g₁ / 4 =
      pairedJ d p g₁ * (target - (base + 3 * h * pairedCount d p g₀ g₁ / 4)) := by
  unfold pairedCount
  field_simp [hJ]
  ring

end

end QRH.Cycle090
