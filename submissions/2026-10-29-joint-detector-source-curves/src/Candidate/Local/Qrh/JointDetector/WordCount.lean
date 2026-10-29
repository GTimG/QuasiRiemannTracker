/- Copyright (c) 2026 Joseph Bebel. -/
import Mathlib

/-!
# The scalar three-witness count envelope

The three ordinary words have length exponents `r`, `2*m` and `r+m`.
This file proves their exact scalar minimax estimate. It asserts neither
the selected ordinary-source norm nor the analytic detector saturation.
-/

namespace Qrh.JointDetector

noncomputable section

def witnessDen (ν δ : ℝ) : ℝ := 3 * (1 - ν) + 2 * (ν - δ)

def mStar (ν δ : ℝ) : ℝ := (1 - δ) / witnessDen ν δ

def lStar (ν δ : ℝ) : ℝ := 2 * mStar ν δ

def hStar (ν δ : ℝ) : ℝ := 3 * mStar ν δ

def jointCountExponent (ν δ : ℝ) : ℝ :=
  3 * (1 - δ) * (1 - ν) / witnessDen ν δ

/-- The exponent supplied by a saturated ordinary word of length `w`. -/
def wordEnvelope (ν δ w : ℝ) : ℝ :=
  max ((1 - ν) * w) ((1 - δ) - (ν - δ) * w)

theorem witnessDen_eq (ν δ : ℝ) : witnessDen ν δ = 3 - ν - 2 * δ := by
  unfold witnessDen
  ring

theorem jointCountExponent_eq (ν δ : ℝ) :
    jointCountExponent ν δ = 3 * (1 - δ) * (1 - ν) / (3 - ν - 2 * δ) := by
  rw [jointCountExponent, witnessDen_eq]

theorem witnessDen_pos {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (501/1000 : ℝ) ν) :
    0 < witnessDen ν δ := by
  dsimp [witnessDen]
  linarith [hν.2, hδ.2]

theorem mStar_pos {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (501/1000 : ℝ) ν) :
    0 < mStar ν δ := by
  exact div_pos (by linarith [hν.2, hδ.2]) (witnessDen_pos hν hδ)

theorem lStar_le_one {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (501/1000 : ℝ) ν) :
    lStar ν δ ≤ 1 := by
  have hd := witnessDen_pos hν hδ
  unfold lStar mStar
  rw [← mul_div_assoc, div_le_iff₀ hd]
  dsimp [witnessDen]
  linarith [hν.2]

theorem one_le_hStar {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (501/1000 : ℝ) ν) :
    1 ≤ hStar ν δ := by
  have hd := witnessDen_pos hν hδ
  unfold hStar mStar
  rw [← mul_div_assoc, le_div_iff₀ hd]
  dsimp [witnessDen]
  linarith [hδ.2]

theorem jointCountExponent_upper_identity (ν δ : ℝ) :
    jointCountExponent ν δ = (1 - ν) * hStar ν δ := by
  unfold jointCountExponent hStar mStar
  ring

theorem jointCountExponent_lower_identity {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (501/1000 : ℝ) ν) :
    jointCountExponent ν δ = (1 - δ) - (ν - δ) * lStar ν δ := by
  have hd := (witnessDen_pos hν hδ).ne'
  unfold jointCountExponent lStar mStar
  field_simp
  unfold witnessDen
  ring

theorem jointCountExponent_bounds {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (501/1000 : ℝ) ν) :
    1 - ν ≤ jointCountExponent ν δ ∧ jointCountExponent ν δ ≤ 1 - δ := by
  have hb : 0 ≤ 1 - ν := by linarith [hν.2]
  have ha : 0 ≤ ν - δ := sub_nonneg.mpr hδ.2
  constructor
  · rw [jointCountExponent_upper_identity]
    nlinarith [mul_le_mul_of_nonneg_left (one_le_hStar hν hδ) hb]
  · rw [jointCountExponent_lower_identity hν hδ]
    have hL : 0 ≤ lStar ν δ := by
      dsimp [lStar]
      positivity [mStar_pos hν hδ]
    linarith [mul_nonneg ha hL]

theorem quarter_le_jointCountExponent {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (501/1000 : ℝ) ν) :
    (1/4 : ℝ) ≤ jointCountExponent ν δ := by
  linarith [hν.2, (jointCountExponent_bounds hν hδ).1]

/-- Every word whose length lies between the two thresholds has exponent at most `e`. -/
theorem wordEnvelope_le_of_mem {ν δ w : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (501/1000 : ℝ) ν)
    (hw : w ∈ Set.Icc (lStar ν δ) (hStar ν δ)) :
    wordEnvelope ν δ w ≤ jointCountExponent ν δ := by
  have hb : 0 ≤ 1 - ν := by linarith [hν.2]
  have ha : 0 ≤ ν - δ := sub_nonneg.mpr hδ.2
  unfold wordEnvelope
  apply max_le
  · rw [jointCountExponent_upper_identity]
    exact mul_le_mul_of_nonneg_left hw.2 hb
  · rw [jointCountExponent_lower_identity hν hδ]
    have := mul_le_mul_of_nonneg_left hw.1 ha
    linarith

/-- At least one of the three actual word lengths meets the good interval.

The nonnegativity assumptions record the intended witness domain; the upper
length and product-length constraints already suffice for this conclusion.
-/
theorem witness_lengths_cover {ν δ r m : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (501/1000 : ℝ) ν)
    (_hr0 : 0 ≤ r) (_hm0 : 0 ≤ m)
    (hr : r ≤ 1) (hm : m ≤ 1/2) (hrm : 1 ≤ r + m) :
    r ∈ Set.Icc (lStar ν δ) (hStar ν δ) ∨
      2 * m ∈ Set.Icc (lStar ν δ) (hStar ν δ) ∨
      r + m ∈ Set.Icc (lStar ν δ) (hStar ν δ) := by
  have hL := lStar_le_one hν hδ
  have hH := one_le_hStar hν hδ
  by_cases hrL : lStar ν δ ≤ r
  · exact Or.inl ⟨hrL, hr.trans hH⟩
  · by_cases hmL : lStar ν δ ≤ 2 * m
    · exact Or.inr (Or.inl ⟨hmL, by linarith⟩)
    · apply Or.inr ∘ Or.inr
      refine ⟨hL.trans hrm, ?_⟩
      have hrL' : r < 2 * mStar ν δ := by
        simpa only [lStar] using lt_of_not_ge hrL
      have hmL' : 2 * m < 2 * mStar ν δ := by
        simpa only [lStar] using lt_of_not_ge hmL
      dsimp [hStar]
      linarith

/-- The three-polynomial scalar count bound, before analytic error buffers. -/
theorem three_word_min_le {ν δ r m : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (501/1000 : ℝ) ν)
    (hr0 : 0 ≤ r) (hm0 : 0 ≤ m)
    (hr : r ≤ 1) (hm : m ≤ 1/2) (hrm : 1 ≤ r + m) :
    min (wordEnvelope ν δ r)
      (min (wordEnvelope ν δ (2 * m)) (wordEnvelope ν δ (r + m))) ≤
        jointCountExponent ν δ := by
  rcases witness_lengths_cover hν hδ hr0 hm0 hr hm hrm with h | h | h
  · exact (min_le_left _ _).trans (wordEnvelope_le_of_mem hν hδ h)
  · exact ((min_le_right _ _).trans (min_le_left _ _)).trans
      (wordEnvelope_le_of_mem hν hδ h)
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans
      (wordEnvelope_le_of_mem hν hδ h)

end

end Qrh.JointDetector
