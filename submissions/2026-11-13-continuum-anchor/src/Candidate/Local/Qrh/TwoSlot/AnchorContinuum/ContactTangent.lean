/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The exact critical tangent is a genuine upper-range paired moment source. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ContactBalance
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.RationalFiber

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section
open Set
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract

def tangentSlope : ℝ := Curve.D 1 (7/9) width
def tangentIntercept : ℝ := gain-tangentSlope*width
def tangent (r : ℝ) : ℝ := tangentIntercept+tangentSlope*r

theorem tangentSlope_bounds : -(4/45:ℝ) ≤ tangentSlope ∧ tangentSlope ≤ 0 := by
  have hw := width_range
  exact Curve.D_bounds (by norm_num) (by norm_num) (by norm_num) le_rfl
    ⟨by linarith,by linarith⟩

theorem tangentSlope_formula : tangentSlope =
    ((15*width-8)*gain+3*width-7/3)/(width*(15*width-10)) := by
  have hw := width_range
  unfold tangentSlope Curve.D
  rw [one_mul]
  change Curve.flow width (ideal width) = _
  rw [←gain_eq_ideal]
  unfold Curve.flow
  rw [Curve.A_eq (by linarith)]
  unfold Curve.b
  ring

/-- The tangent supports the whole interval, including points to the left
of contact. This uses convexity, rather than a sampled comparison. -/
theorem tangent_minorant {r : ℝ} (hr : r ∈ Icc (3/4:ℝ) (7/9)) :
    tangent r ≤ ideal r := by
  have hw := width_range
  have hW : Curve.W 1 (7/9) width = gain := by
    simpa only [Curve.W,one_mul,ideal] using gain_eq_ideal.symm
  have hWr : Curve.W 1 (7/9) r = ideal r := by
    simp only [Curve.W,one_mul,ideal]
  by_cases hgt : width < r
  · have hh := Curve.tangent_previous (lam := 1) (T := 7/9)
      (by norm_num) (by linarith) hgt hr.2
    rw [hW,hWr] at hh
    unfold tangent tangentIntercept tangentSlope
    linarith
  · by_cases he : r = width
    · subst r
      unfold tangent tangentIntercept
      rw [gain_eq_ideal]
      ring_nf
      exact le_rfl
    · have hlt : r < width := lt_of_le_of_ne (le_of_not_gt hgt) he
      have hc := Curve.convex_W (lam := 1) (T := 7/9) (by norm_num) (by norm_num)
      have hh := hc.slope_le_of_hasDerivAt hr ⟨by linarith,by linarith⟩ hlt
        (Curve.hasDerivAt_W 1 (7/9) (by linarith : 2/3 < width))
      rw [slope_def_field,hW,hWr] at hh
      have hm := (div_le_iff₀ (sub_pos.mpr hlt)).mp hh
      unfold tangent tangentIntercept tangentSlope
      linarith

def exactLine : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line where
  g0 := tangentIntercept
  g1 := -tangentSlope
  slope_nonneg := by linarith [tangentSlope_bounds.2]
  slope_le := by linarith [tangentSlope_bounds.1]

/-- Actual paired moments for the exact tangent, with the existing classical
lower-beta case and no new analytic estimate. -/
theorem tangent_upper_moments
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    ImprovedMoments (3/4) (311/400) exactLine.g0 exactLine.g1 := by
  intro r hlo hhi
  have hs := ideal_anchor pr103Face hβ (Reserve.reserveParametricSource hβ)
    (Driver.pr103_parent hβ) hlo (by linarith)
  have hm := tangent_minorant (r := r) ⟨hlo,by linarith⟩
  apply hs.mono le_rfl
  change (1-r)/2+(tangentIntercept-(-tangentSlope)*r) ≤ _
  unfold tangent at hm
  linarith

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.tangent_minorant
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.tangent_upper_moments
