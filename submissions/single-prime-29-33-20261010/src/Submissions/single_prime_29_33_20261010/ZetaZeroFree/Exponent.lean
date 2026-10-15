import Mathlib.Basic.Real.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Exact exponent arithmetic for §§2.1 and 5 of
`zeta_zero_free_4_33_self_contained.md`.

These results establish the rational inequalities only. In particular they do
not assert the row estimates, contour shifts, or Mellin continuation used in
the manuscript's analytic argument.
-/

namespace ZetaZeroFree.Exponent

noncomputable section

def x : ℝ := 13 / 33
def y : ℝ := 15 / 33
def ell : ℝ := 5 / 33
def h : ℝ := 1 + ell - x
def k : ℝ := 5 / 6 - x / 3 - ell / 6
def b : ℝ := 29 / 33
def z0 : ℝ := 17 / 50
def dmin : ℝ := 1 / 200

theorem scale_values :
    x = 13 / 33 ∧ y = 15 / 33 ∧ ell = 5 / 33 ∧
      h = 25 / 33 ∧ k = 67 / 99 := by
  norm_num [x, y, ell, h, k]

theorem physical_exponent : b - k = 20 / 99 := by
  norm_num [b, k, x, ell]

theorem physical_exponent_from_scales : x / 2 + (y - x) / 12 = 20 / 99 := by
  norm_num [x, y]

theorem principal_savings_positive : 0 < y / 4 ∧ 0 < h / 24 := by
  norm_num [y, h, x, ell]

theorem original_boundary_comparison : (7 / 8 : ℝ) < b := by
  norm_num [b]

theorem original_boundary_gap : b - 7 / 8 = 1 / 264 := by
  norm_num [b]

def a (delta : ℝ) : ℝ := (1 + delta) / 2

def R0 (delta : ℝ) : ℝ := 1 - 10 * delta / (3 * (5 - 2 * delta))

def F0 (delta : ℝ) : ℝ :=
  (16 / 11) * a delta + (25 / 33) * (R0 delta - 2 / 3) - 5 / 33

def slope (delta : ℝ) : ℝ := R0 delta + delta / 2 - z0

def E (delta beta d : ℝ) : ℝ :=
  a delta - beta + h * (z0 - 1 / 6) - a delta * y - ell / 2 +
    ell * delta / 2 + d * slope delta

theorem denominator_positive {delta : ℝ} (hupper : delta ≤ 5 / 6) :
    0 < 5 - 2 * delta := by
  linarith

theorem certificate_denominator_positive {delta : ℝ} (hupper : delta ≤ 5 / 6) :
    0 < 99 * (5 - 2 * delta) := by
  have := denominator_positive hupper
  positivity

/-- The square identity needs only a nonzero denominator, not a row estimate. -/
theorem square_certificate {delta : ℝ} (hden : 5 - 2 * delta ≠ 0) :
    b - F0 delta = (12 * delta - 5) ^ 2 / (99 * (5 - 2 * delta)) := by
  have hden' : 5 - delta * 2 ≠ 0 := by simpa [mul_comm] using hden
  unfold b F0 a R0
  field_simp [hden, hden']
  ring

theorem F0_le_boundary {delta : ℝ} (hupper : delta ≤ 5 / 6) :
    F0 delta ≤ b := by
  have hden := denominator_positive hupper
  have hcert := square_certificate (ne_of_gt hden)
  have hnonneg : 0 ≤ (12 * delta - 5) ^ 2 / (99 * (5 - 2 * delta)) := by
    positivity
  linarith

theorem F0_eq_boundary_iff {delta : ℝ} (hupper : delta ≤ 5 / 6) :
    F0 delta = b ↔ delta = 5 / 12 := by
  have hden := certificate_denominator_positive hupper
  have hcert := square_certificate (ne_of_gt (denominator_positive hupper))
  constructor
  · intro heq
    have hquot : (12 * delta - 5) ^ 2 / (99 * (5 - 2 * delta)) = 0 := by
      linarith
    have hsquare : (12 * delta - 5) ^ 2 = 0 :=
      ((div_eq_zero_iff).mp hquot).resolve_right (ne_of_gt hden)
    have hzero : 12 * delta - 5 = 0 := (sq_eq_zero_iff).mp hsquare
    linarith
  · intro heq
    subst delta
    norm_num [F0, a, R0, b]

/-- The lower bound used for the positive slope holds on the stated row interval. -/
theorem R0_lower {delta : ℝ} (hlower : 0 ≤ delta) (hupper : delta ≤ 5 / 6) :
    1 - delta ≤ R0 delta := by
  have hden : 0 < 3 * (5 - 2 * delta) := by
    have := denominator_positive hupper
    positivity
  have hprod : 0 ≤ delta * (5 - 6 * delta) :=
    mul_nonneg hlower (by linarith)
  have hquot : 10 * delta / (3 * (5 - 2 * delta)) ≤ delta := by
    apply (div_le_iff₀ hden).2
    nlinarith
  unfold R0
  linarith

theorem slope_lower {delta : ℝ} (hlower : 0 ≤ delta) (hupper : delta ≤ 5 / 6) :
    (73 / 300 : ℝ) ≤ slope delta := by
  have hR := R0_lower hlower hupper
  unfold slope z0
  linarith

theorem slope_positive {delta : ℝ} (hlower : 0 ≤ delta) (hupper : delta ≤ 5 / 6) :
    0 < slope delta := by
  have := slope_lower hlower hupper
  linarith

theorem E_at_h (delta beta : ℝ) : E delta beta h = F0 delta - beta := by
  unfold E slope F0 a h x y ell z0
  ring

theorem E_difference (delta beta d : ℝ) :
    E delta beta h - E delta beta d = (h - d) * slope delta := by
  unfold E
  ring

theorem E_le_at_h {delta beta d : ℝ} (hlower : 0 ≤ delta)
    (hupper : delta ≤ 5 / 6) (hd : d ≤ h) :
    E delta beta d ≤ E delta beta h := by
  have hslope := le_of_lt (slope_positive hlower hupper)
  have hprod := mul_nonneg (sub_nonneg.mpr hd) hslope
  have hdiff := E_difference delta beta d
  linarith

theorem E_le_boundary {delta beta d : ℝ} (hlower : 0 ≤ delta)
    (hupper : delta ≤ 5 / 6) (hd : d ≤ h) :
    E delta beta d ≤ b - beta := by
  have hrow := E_le_at_h (beta := beta) hlower hupper hd
  have hF := F0_le_boundary hupper
  rw [E_at_h] at hrow
  linarith

theorem E_strict_saving {delta beta d : ℝ} (hlower : 0 ≤ delta)
    (hupper : delta ≤ 5 / 6) (hd : d ≤ h) (hbeta : b < beta) :
    E delta beta d < 0 := by
  have := E_le_boundary (beta := beta) hlower hupper hd
  linarith

/-- An explicit version of the shorter-row margin, before analytic losses. -/
theorem E_saving_margin {delta beta d mu : ℝ} (hlower : 0 ≤ delta)
    (hupper : delta ≤ 5 / 6) (hd : d ≤ h) (hmu : mu = beta - b) :
    E delta beta d ≤ -mu := by
  have := E_le_boundary (beta := beta) hlower hupper hd
  linarith

def smallRowExponent : ℝ := h * (z0 - 1 / 6) - y / 2 + (63 / 50) * dmin

theorem small_row_exact : smallRowExponent = -(88763 / 990000 : ℝ) := by
  norm_num [smallRowExponent, h, x, ell, z0, y, dmin]

theorem small_row_saving : smallRowExponent < -(1 / 20 : ℝ) := by
  rw [small_row_exact]
  norm_num

theorem dmin_in_range : 0 < dmin ∧ dmin ≤ h := by
  norm_num [dmin, h, x, ell]

/-- For the floor row the count exponent is one and a = 51/100. -/
def floorBoundary : ℝ := (16 / 11) * (51 / 100) + (25 / 33) * (1 - 2 / 3) - 5 / 33

theorem floor_gap : b - floorBoundary = 89 / 2475 := by
  norm_num [b, floorBoundary]

theorem floor_saving : floorBoundary < b := by
  have := floor_gap
  linarith

/--
The analytic argument must provide one positive `Delta` that bounds every
element of `S`. This hypothesis isolates that quantifier obligation; it does
not establish any analytic estimate. The supremum need not belong to `S`.
-/
theorem supremum_le_of_common_saving {S : Set ℝ} {beta boundary : ℝ}
    (hsup : IsLUB S beta)
    (analytic_common_saving : boundary < beta →
      ∃ Delta : ℝ, 0 < Delta ∧ ∀ t ∈ S, t ≤ beta - Delta) :
    beta ≤ boundary := by
  by_contra hnot
  have hstrict : boundary < beta := lt_of_not_ge hnot
  obtain ⟨Delta, hDelta, hbound⟩ := analytic_common_saving hstrict
  have hupper : beta - Delta ∈ upperBounds S := by
    intro t ht
    exact hbound t ht
  have hle : beta ≤ beta - Delta := hsup.2 hupper
  linarith

end

end ZetaZeroFree.Exponent
