/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The checked finite source with all seed, parent and reserve obligations discharged.
The native top extension retains every positive rectangle decrement. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.FiniteInduction
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Driver.Parent
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Reserve.TopAnchors

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorZeroLoss
open OAI.SevenEighths Qrh.MarkedAnchor.Interface.Contract
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price

/-- Actual finite paired source under the same classical lower-beta case split
as the inherited unconditional proof. No additional arithmetic premise remains. -/
theorem finite_source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ImprovedMoments (1467/2000) (311/400)
      (Certificate.targetG0:ℝ) (Certificate.targetG1:ℝ) :=
  Certificate.finite_improved_moments pr103Face hβ
    (Reserve.reserveParametricSource hβ) (Driver.pr103_parent hβ)
    (Reserve.base_anchor_native hβ)

/-- A small native extension above the final stage's top avoids claiming an
open rectangle controls its own excluded upper free-width endpoint. -/
theorem finite_source_top (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ImprovedMoments (311/400) (311/400+1/1000)
      (Certificate.targetG0:ℝ) (Certificate.targetG1:ℝ) := by
  intro r hr1 hr2
  have hz : (Certificate.targetG0:ℝ)-(Certificate.targetG1:ℝ)*r ≤ -9/10000 := by
    norm_num [Certificate.targetG0,Certificate.targetG1] at *
    linarith
  have hz' : -2/1000 ≤ (Certificate.targetG0:ℝ)-(Certificate.targetG1:ℝ)*r := by
    norm_num [Certificate.targetG0,Certificate.targetG1] at *
    linarith
  apply AnchorAt.of_small (δ₀ := 1/100) (by norm_num)
  intro δ hδ hδ1
  refine ⟨Inverse.inverseRectSource_native canonicalFamily ?_, ?_⟩
  · constructor <;> simp only [anchorRect] <;> linarith
  · obtain ⟨B,L,c,hsrc,hL0,hL,hB,hc⟩ := Reserve.reserveParametricSource hβ δ hδ
    apply ordinaryRectSource_of_global hsrc hL0
    · simp only [anchorRect]
      have hS0 : 0 ≤ (1-r)/2+
          ((Certificate.targetG0:ℝ)-(Certificate.targetG1:ℝ)*r)-δ := by linarith
      have hS1 : (1-r)/2+
          ((Certificate.targetG0:ℝ)-(Certificate.targetG1:ℝ)*r)-δ ≤ 1/8 := by linarith
      have h1 := mul_le_mul_of_nonneg_right hL hS0
      have h2 := mul_le_mul_of_nonneg_left hS1 hδ.le
      nlinarith
    · simp only [anchorRect]
      linarith

end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.finite_source
#print axioms Qrh.TwoSlot.AnchorZeroLoss.finite_source_top
