/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Complete paired source and detector-fiber contract for the exact tangent. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.TangentBounds

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract

theorem padded_lower_checked : ∀ i : Fin 113,
    RationalSource.lowerCheck (8079+i.val) (1/10000000) := by decide +kernel

theorem tangent_lower_comparison {r : ℝ} (hlo : 1467/2000 ≤ r) (hhi : r ≤ 3/4) :
    tangent r ≤ ((RationalSource.g0+(1/10000000:ℚ):ℚ):ℝ)-(RationalSource.g1:ℝ)*r := by
  have hc := tangent_coefficient_bounds
  have hp := mul_le_mul_of_nonneg_right hc.2.2.1.le (show 0 ≤ r by linarith)
  unfold tangent
  norm_num [RationalSource.g0,RationalSource.g1]
  nlinarith [hc.1]

theorem tangent_lower_moments
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    ImprovedMoments (1467/2000) (3/4) exactLine.g0 exactLine.g1 := by
  intro r hlo hhi
  have hs := RationalSource.lower_moments_with_pad (1/10000000) padded_lower_checked hβ r hlo hhi
  have hm := tangent_lower_comparison hlo hhi
  apply hs.mono le_rfl
  change (1-r)/2+(tangentIntercept-(-tangentSlope)*r) ≤ _
  unfold tangent at hm
  linarith

theorem tangent_full_moments
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    ImprovedMoments (1467/2000) (311/400) exactLine.g0 exactLine.g1 := by
  intro r hlo hhi
  by_cases hr : r ≤ 3/4
  · exact tangent_lower_moments hβ r hlo hr
  · exact tangent_upper_moments hβ r (le_of_not_ge hr) hhi

theorem tangent_top_moments
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    ImprovedMoments (311/400) (311/400+1/1000) exactLine.g0 exactLine.g1 := by
  intro r hr1 hr2
  have hc := tangent_coefficient_bounds
  have hm0 := mul_le_mul_of_nonneg_right hc.2.2.1.le (show 0 ≤ r by linarith)
  have hm1 := mul_le_mul_of_nonneg_right hc.2.2.2.le (show 0 ≤ r by linarith)
  have hz : exactLine.g0-exactLine.g1*r ≤ -9/10000 := by
    change tangentIntercept-(-tangentSlope)*r ≤ _
    nlinarith [hc.2.1]
  have hz' : -2/1000 ≤ exactLine.g0-exactLine.g1*r := by
    change _ ≤ tangentIntercept-(-tangentSlope)*r
    nlinarith [hc.1]
  apply AnchorAt.of_small (δ₀ := 1/100) (by norm_num)
  intro δ hδ hδ1
  refine ⟨Inverse.inverseRectSource_native canonicalFamily ?_, ?_⟩
  · constructor <;> simp only [anchorRect] <;> linarith
  · obtain ⟨B,L,c,hsrc,hL0,hL,hB,hc⟩ := Reserve.reserveParametricSource hβ δ hδ
    apply ordinaryRectSource_of_global hsrc hL0
    · simp only [anchorRect]
      have hS0 : 0 ≤ (1-r)/2+(exactLine.g0-exactLine.g1*r)-δ := by linarith
      have hS1 : (1-r)/2+(exactLine.g0-exactLine.g1*r)-δ ≤ 1/8 := by linarith
      have h1 := mul_le_mul_of_nonneg_right hL hS0
      have h2 := mul_le_mul_of_nonneg_left hS1 hδ.le
      nlinarith
    · simp only [anchorRect]
      linarith

theorem exact_fiber_moments
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    Qrh.TwoSlot.AnchorZeroLoss.Affine.ImprovedFiberMoments exactLine := by
  apply Qrh.TwoSlot.AnchorZeroLoss.Affine.fiber_of_improved_split exactLine
    (hi := 311/400+1/1000) (by norm_num [Qrh.MarkedAnchor.Interface.anchorTop])
  · exact tangent_full_moments hβ
  · exact tangent_top_moments hβ

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.exact_fiber_moments
