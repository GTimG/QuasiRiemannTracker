/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The rational continuum line as an actual paired moment supplier. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.RationalSource
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.FiniteSource
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.LowerPatch

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.RationalSource
noncomputable section
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract

/-- No new analytic premise remains in the upper part of the rational source.
The classical lower-beta case is the same as in the complete finite endpoint. -/
theorem upper_moments
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    ImprovedMoments (3/4) (311/400) (g0:ℝ) (g1:ℝ) := by
  intro r hlo hhi
  have hsource := ideal_anchor pr103Face hβ
    (Reserve.reserveParametricSource hβ) (Driver.pr103_parent hβ) hlo
    (by linarith : r < 7/9)
  apply hsource.mono le_rfl
  have hminor := upper_minorant hlo hhi
  unfold line at hminor
  linarith

theorem full_moments
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    ImprovedMoments (1467/2000) (311/400) (g0:ℝ) (g1:ℝ) := by
  intro r hlo hhi
  by_cases hr : r ≤ 3/4
  · exact lower_moments hβ r hlo hr
  · exact upper_moments hβ r (le_of_not_ge hr) hhi

/-- The source's open upper endpoint is supplied by a native rectangle,
with its own arbitrary positive decrement. -/
theorem top_moments
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    ImprovedMoments (311/400) (311/400+1/1000) (g0:ℝ) (g1:ℝ) := by
  intro r hr1 hr2
  have hz : (g0:ℝ)-(g1:ℝ)*r ≤ -9/10000 := by
    norm_num [g0,g1] at *
    linarith
  have hz' : -2/1000 ≤ (g0:ℝ)-(g1:ℝ)*r := by
    norm_num [g0,g1] at *
    linarith
  apply AnchorAt.of_small (δ₀ := 1/100) (by norm_num)
  intro δ hδ hδ1
  refine ⟨Inverse.inverseRectSource_native canonicalFamily ?_, ?_⟩
  · constructor <;> simp only [anchorRect] <;> linarith
  · obtain ⟨B,L,c,hsrc,hL0,hL,hB,hc⟩ := Reserve.reserveParametricSource hβ δ hδ
    apply ordinaryRectSource_of_global hsrc hL0
    · simp only [anchorRect]
      have hS0 : 0 ≤ (1-r)/2+((g0:ℝ)-(g1:ℝ)*r)-δ := by linarith
      have hS1 : (1-r)/2+((g0:ℝ)-(g1:ℝ)*r)-δ ≤ 1/8 := by linarith
      have h1 := mul_le_mul_of_nonneg_right hL hS0
      have h2 := mul_le_mul_of_nonneg_left hS1 hδ.le
      nlinarith
    · simp only [anchorRect]
      linarith

end
end Qrh.TwoSlot.AnchorContinuum.RationalSource
#print axioms Qrh.TwoSlot.AnchorContinuum.RationalSource.upper_moments
#print axioms Qrh.TwoSlot.AnchorContinuum.RationalSource.full_moments
#print axioms Qrh.TwoSlot.AnchorContinuum.RationalSource.top_moments
