/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Mathlib

set_option autoImplicit false
namespace Sil.Uneven.RowInterpolation

theorem affine_between (a b lo hi z bound : ℝ)
    (hz : lo ≤ z ∧ z ≤ hi)
    (hlo : a+b*lo ≤ bound) (hhi : a+b*hi ≤ bound) :
    a+b*z ≤ bound := by
  by_cases hb : 0 ≤ b
  · have hh := mul_le_mul_of_nonneg_left hz.2 hb
    linarith only [hh,hhi]
  · have hh := mul_le_mul_of_nonpos_left hz.1 (le_of_not_ge hb)
    linarith only [hh,hlo]

/-- A nonnegative multiple of a minimum of two affine capacities is
subtracted. Thus both endpoint inequalities control the entire interval. -/
theorem min_capacity_between (a b w c₀ c₁ e₀ e₁ lo hi z bound : ℝ)
    (hw : 0 ≤ w) (hz : lo ≤ z ∧ z ≤ hi)
    (hlo : a+b*lo-w*min (c₀+c₁*lo) (e₀+e₁*lo) ≤ bound)
    (hhi : a+b*hi-w*min (c₀+c₁*hi) (e₀+e₁*hi) ≤ bound) :
    a+b*z-w*min (c₀+c₁*z) (e₀+e₁*z) ≤ bound := by
  have hl₀ := mul_le_mul_of_nonneg_left (min_le_left (c₀+c₁*lo) (e₀+e₁*lo)) hw
  have hl₁ := mul_le_mul_of_nonneg_left (min_le_left (c₀+c₁*hi) (e₀+e₁*hi)) hw
  have hr₀ := mul_le_mul_of_nonneg_left (min_le_right (c₀+c₁*lo) (e₀+e₁*lo)) hw
  have hr₁ := mul_le_mul_of_nonneg_left (min_le_right (c₀+c₁*hi) (e₀+e₁*hi)) hw
  have hl : a+b*z-w*(c₀+c₁*z) ≤ bound := by
    have hh := affine_between (a-w*c₀) (b-w*c₁) lo hi z bound hz
      (by nlinarith only [hl₀,hlo]) (by nlinarith only [hl₁,hhi])
    nlinarith only [hh]
  have hr : a+b*z-w*(e₀+e₁*z) ≤ bound := by
    have hh := affine_between (a-w*e₀) (b-w*e₁) lo hi z bound hz
      (by nlinarith only [hr₀,hlo]) (by nlinarith only [hr₁,hhi])
    nlinarith only [hh]
  rcases le_total (c₀+c₁*z) (e₀+e₁*z) with h | h
  · rw [min_eq_left h]
    exact hl
  · rw [min_eq_right h]
    exact hr

end Sil.Uneven.RowInterpolation
