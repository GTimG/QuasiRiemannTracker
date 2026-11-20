/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The exact ordered source envelope in P1

This file formalizes the piecewise polynomial envelope and its elementary
properties. It does not assert that an analytic marked energy admits that
envelope: the analytic source induction and selected-cell input remain
separate obligations. The recovered 31,680 finite tests are formalized in
`SourceCertificate`, with their real scalar cover in `SourceContinuum`. Appendix Q uses this same envelope without change.
-/

set_option autoImplicit false

namespace QRH.Cycle090

noncomputable section

/-- Lower ordinary source label `Y₀ = 0.369` in P.1. -/
def sourceY0 : ℝ := 369 / 1000

/-- Upper ordinary source label `Y = 0.3888` in P.1. -/
def sourceY : ℝ := 243 / 625

/-- The seam `a = 0.3735` in the piecewise source gain. -/
def sourceSeam : ℝ := 747 / 2000

/-- The largest ratio of ordered labels, `λ = 1.15`. -/
def sourceRatio : ℝ := 23 / 20

/-- Cubic branch of the ordered source gain P1. -/
def upperGain (y : ℝ) : ℝ :=
  (2309 / 500) * (sourceY - y) ^ 2 + (101 / 2) * (sourceY - y) ^ 3 +
    (31 / 100000) * (sourceY - y) - 1 / 10000000

/-- Quadratic branch below the seam, joined at the actual cubic value. -/
def lowerGain (y : ℝ) : ℝ :=
  upperGain sourceSeam + (87 / 500) * (sourceSeam - y) +
    (67 / 10) * (sourceSeam - y) ^ 2

/-- The piecewise gain `F` in P1, with the upper branch at the seam. -/
def sourceGain (y : ℝ) : ℝ :=
  if sourceSeam ≤ y then upperGain y else lowerGain y

/-- The pre-division source envelope `W(n,y)` in P1. -/
def sourceWidth (n y : ℝ) : ℝ := (1 - n - y) / 2 + sourceGain y

/-- The derivative polynomial on the cubic branch. -/
def upperGainSlope (y : ℝ) : ℝ :=
  -((2309 / 250) * (sourceY - y) +
    (303 / 2) * (sourceY - y) ^ 2 + 31 / 100000)

/-- The derivative polynomial on the quadratic branch. -/
def lowerGainSlope (y : ℝ) : ℝ :=
  -(87 / 500) - (67 / 5) * (sourceSeam - y)

/-- The source domain contains the seam strictly. -/
theorem source_domain : 0 < sourceY0 ∧ sourceY0 < sourceSeam ∧ sourceSeam < sourceY := by
  norm_num [sourceY0, sourceSeam, sourceY]

/-- The two polynomial branches have exactly the same value at the seam. -/
theorem source_seam_join : lowerGain sourceSeam = upperGain sourceSeam := by
  simp [lowerGain]

/-- The gain at the native endpoint is negative, as used for the starting strip. -/
theorem source_native_value : sourceGain sourceY = -(1 / 10000000 : ℝ) := by
  rw [sourceGain, ite_eq_left source_domain.2.2.le]
  simp [upperGain]

/-- The cubic gain is nonincreasing up to the native endpoint. -/
theorem upperGain_antitone {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (hy₂ : y₂ ≤ sourceY) :
    upperGain y₂ ≤ upperGain y₁ := by
  have hr₂ : 0 ≤ sourceY - y₂ := sub_nonneg.mpr hy₂
  unfold upperGain
  gcongr

/-- The quadratic gain is nonincreasing below its seam. -/
theorem lowerGain_antitone {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (hy₂ : y₂ ≤ sourceSeam) :
    lowerGain y₂ ≤ lowerGain y₁ := by
  have hr₂ : 0 ≤ sourceSeam - y₂ := sub_nonneg.mpr hy₂
  unfold lowerGain
  gcongr

/-- The complete joined envelope is nonincreasing on its source interval. -/
theorem sourceGain_antitone {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (hy₂ : y₂ ≤ sourceY) :
    sourceGain y₂ ≤ sourceGain y₁ := by
  by_cases h₁ : sourceSeam ≤ y₁
  · have h₂ : sourceSeam ≤ y₂ := h₁.trans hy
    simpa only [sourceGain, ite_eq_left h₁, ite_eq_left h₂] using upperGain_antitone hy hy₂
  · by_cases h₂ : sourceSeam ≤ y₂
    · have hupper := upperGain_antitone h₂ hy₂
      have hlower := lowerGain_antitone (le_of_not_ge h₁) (le_refl sourceSeam)
      rw [source_seam_join] at hlower
      simpa only [sourceGain, ite_eq_right h₁, ite_eq_left h₂] using hupper.trans hlower
    · simpa only [sourceGain, ite_eq_right h₁, ite_eq_right h₂] using
        lowerGain_antitone hy (le_of_not_ge h₂)

/-- Both upper labels may be shortened without reducing the available algebraic width. -/
theorem sourceWidth_mono_shortening {n₁ n₂ y₁ y₂ : ℝ}
    (hn : n₁ ≤ n₂) (hy : y₁ ≤ y₂) (hy₂ : y₂ ≤ sourceY) :
    sourceWidth n₂ y₂ ≤ sourceWidth n₁ y₁ := by
  have hg := sourceGain_antitone hy hy₂
  unfold sourceWidth
  linarith

/-- The cubic branch has the displayed derivative. -/
theorem upperGain_hasDerivAt (y : ℝ) : HasDerivAt upperGain (upperGainSlope y) y := by
  have hr : HasDerivAt (fun z : ℝ => sourceY - z) (-1) y :=
    (hasDerivAt_id y).const_sub sourceY
  unfold upperGain upperGainSlope
  convert ((((hr.pow 2).const_mul (2309 / 500)).add
    ((hr.pow 3).const_mul (101 / 2))).add
    (hr.const_mul (31 / 100000))).sub_const (1 / 10000000) using 1
  norm_num
  ring

/-- The lower quadratic branch has the displayed derivative. -/
theorem lowerGain_hasDerivAt (y : ℝ) : HasDerivAt lowerGain (lowerGainSlope y) y := by
  have hr : HasDerivAt (fun z : ℝ => sourceSeam - z) (-1) y :=
    (hasDerivAt_id y).const_sub sourceSeam
  unfold lowerGain lowerGainSlope
  convert ((hr.const_mul (87 / 500)).const_add (upperGain sourceSeam)).add
    ((hr.pow 2).const_mul (67 / 10)) using 1
  norm_num
  ring

/-- The cubic branch's derivative is strictly between `-1/4` and zero. -/
theorem upperGain_slope_bounds {y : ℝ}
    (ha : sourceSeam ≤ y) (hY : y ≤ sourceY) :
    -(1 / 4 : ℝ) < upperGainSlope y ∧ upperGainSlope y < 0 := by
  have hr0 : 0 ≤ sourceY - y := sub_nonneg.mpr hY
  have hr1 : sourceY - y ≤ 153 / 10000 := by
    norm_num [sourceY, sourceSeam] at ha ⊢
    linarith
  have hr2 : (sourceY - y) ^ 2 ≤ (153 / 10000 : ℝ) ^ 2 := by
    nlinarith
  unfold upperGainSlope
  constructor <;> nlinarith [sq_nonneg (sourceY - y)]

/-- The lower branch's derivative is strictly between `-1/4` and zero. -/
theorem lowerGain_slope_bounds {y : ℝ}
    (hlo : sourceY0 ≤ y) (ha : y ≤ sourceSeam) :
    -(1 / 4 : ℝ) < lowerGainSlope y ∧ lowerGainSlope y < 0 := by
  norm_num [sourceY0, sourceSeam, lowerGainSlope] at hlo ha ⊢
  constructor <;> linarith

/-- The branch slopes do not match at the seam; no global convexity is asserted. -/
theorem source_downward_slope_jump :
    upperGainSlope sourceSeam < lowerGainSlope sourceSeam := by
  norm_num [upperGainSlope, lowerGainSlope, sourceY, sourceSeam]

/-- Exact low-response cancellation in P3 at `H = 1 - 6u`. -/
theorem low_response_cancellation {n y u H : ℝ}
    (hH : H = 1 - 6 * u) (hH0 : H ≠ 0) :
    sourceWidth n y - u - H * sourceWidth (n / H) (y / H) =
      2 * u + sourceGain y - H * sourceGain (y / H) := by
  unfold sourceWidth
  field_simp
  nlinarith [hH]

/-- The ordered reference label stays inside the ratio corridor in the swapped case. -/
theorem source_swap_ratio {n y m H : ℝ}
    (hH : 0 < H) (hy0 : sourceY0 ≤ y) (hyH : y / H ≤ m)
    (hmY : m ≤ sourceY) (hnlo : y ≤ n) (hnhi : n ≤ sourceRatio * y)
    (hH1 : H ≤ 1) :
    n / H ≤ sourceRatio * m ∧ m ≤ sourceRatio * (n / H) := by
  have hypos : 0 < y := lt_of_lt_of_le source_domain.1 hy0
  have hny : y ≤ n / H := by
    apply (le_div_iff₀ hH).2
    have hh : y * H ≤ y := mul_le_of_le_one_right hypos.le hH1
    exact hh.trans hnlo
  have hrat : 0 ≤ sourceRatio := by norm_num [sourceRatio]
  constructor
  · apply (div_le_iff₀ hH).2
    have hmul := mul_le_mul_of_nonneg_left hyH hrat
    have hyDiv : n / H ≤ sourceRatio * (y / H) := by
      apply (div_le_iff₀ hH).2
      field_simp
      exact hnhi
    exact (div_le_iff₀ hH).mp (hyDiv.trans hmul)
  · have hsource : sourceY ≤ sourceRatio * sourceY0 := by
      norm_num [sourceY, sourceRatio, sourceY0]
    exact hmY.trans (hsource.trans (mul_le_mul_of_nonneg_left (hy0.trans hny) hrat))

/-- The maximal algebraic source width over the ordered admissible labels. -/
def sourceWMax : ℝ := sourceWidth sourceY0 sourceY0

/-- The exact value of the maximal source width used by the crude source guards. -/
theorem sourceWMax_value : sourceWMax = 266370430517 / 2000000000000 := by
  norm_num [sourceWMax, sourceWidth, sourceGain, lowerGain, upperGain,
    sourceY0, sourceY, sourceSeam]

/-- The source envelope is bounded by its exact lower-label corner. -/
theorem sourceWidth_le_max {n y : ℝ}
    (hy : sourceY0 ≤ y) (hY : y ≤ sourceY) (hn : y ≤ n) :
    sourceWidth n y ≤ sourceWMax :=
  sourceWidth_mono_shortening (hy.trans hn) hy hY

/-- Even the smallest admissible algebraic width is strictly positive. -/
theorem sourceWidth_positive {n y : ℝ}
    (hY : y ≤ sourceY) (hn : n ≤ sourceRatio * y) : 0 < sourceWidth n y := by
  have hr : 0 ≤ sourceRatio := by norm_num [sourceRatio]
  have hng : n ≤ sourceRatio * sourceY :=
    hn.trans (mul_le_mul_of_nonneg_left hY hr)
  have hl := sourceWidth_mono_shortening hng hY (le_refl sourceY)
  have he : 0 < sourceWidth (sourceRatio * sourceY) sourceY := by
    rw [sourceWidth, source_native_value]
    norm_num [sourceRatio, sourceY]
  exact he.trans_le hl

/-- Source induction cost `u = 3 · 10⁻⁶` from P.1. -/
def sourceU : ℝ := 3 / 1000000

/-- The regular-core cutoff `H = 1 - 6u` from P.1. -/
def sourceH : ℝ := 1 - 6 * sourceU

/-- Source strict reserve `ρ = 2 · 10⁻¹¹` from P.1. -/
def sourceRho : ℝ := 1 / 50000000000

/-- The short marked reference `b_ref = .115` from P.3. -/
def shortReference : ℝ := 23 / 200

/-- The nonprincipal marked-reference conductor has the stated strict spare. -/
theorem short_reference_conductor_guard :
    (724 / 100000 : ℝ) < sourceH - 4 * (shortReference + sourceWMax) := by
  rw [sourceWMax_value]
  norm_num [sourceH, sourceU, shortReference]

/-- The equal-product reference companion has exactly the stated exponent. -/
theorem reference_companion_value :
    (1 + sourceRatio) * sourceY - shortReference = 18023 / 25000 := by
  norm_num [sourceRatio, sourceY, shortReference]

/-- The fixed-row numerical guard P7, conditional only on the displayed bound for `A₀`. -/
theorem fixed_row_guard {A₀ : ℝ} (hA : A₀ ≤ 9179599 / 10000000) :
    A₀ + 3 * sourceU - 5 / 6 - shortReference < -(3036 / 100000 : ℝ) := by
  norm_num [sourceU, shortReference]
  linarith

/-- The high native-radius edge in P.2 has strictly positive scalar reserve. -/
theorem native_radial_edge :
    (3 / 4 : ℝ) * ((1 - 98 / 100) / 2 + sourceGain sourceY0 - sourceU) <
      sourceU - sourceRho + (5 / 6) * (sourceH - 98 / 100) := by
  norm_num [sourceGain, lowerGain, upperGain, sourceY0, sourceY, sourceSeam,
    sourceU, sourceH, sourceRho]

/-- The middle native-radius edge in P.2 has strictly positive scalar reserve. -/
theorem middle_radial_edge :
    (3 / 4 : ℝ) * (sourceWMax - sourceU) <
      sourceU - sourceRho + (5 / 6) * (sourceH - 7 / 8) := by
  rw [sourceWMax_value]
  norm_num [sourceU, sourceH, sourceRho]

/-- The smallest-radius pointwise edge in P.2 has strictly positive scalar reserve. -/
theorem small_radial_edge :
    (3 / 4 : ℝ) * ((1 + sourceRatio) * sourceY) + sourceWMax - sourceU <
      sourceU - sourceRho + (5 / 6) * (sourceH - 2 / 25) := by
  rw [sourceWMax_value]
  norm_num [sourceU, sourceH, sourceRho, sourceRatio, sourceY]

end

end QRH.Cycle090
