/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The native paired source permits seeds approaching 7/9. Both moments retain
all positive rectangle decrements and their original physical contracts. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Reserve.TopAnchors

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorContinuum
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Interface.Contract
open Qrh.MarkedAnchor.Interface.Native

/-- The literal old top was a construction choice, not a native-source limit. -/
theorem native_seed_of_reserve (hres : ReserveParametricSource) {R : ℝ}
    (hR : 7/10 ≤ R) (hR1 : R < 1) : AnchorAt R 0 := by
  let δ₀ := min ((1-R)/4) (1/100)
  have hδ₀ : 0 < δ₀ := lt_min (by linarith) (by norm_num)
  apply AnchorAt.of_small hδ₀
  intro δ hδ hsmall
  have hdR : δ ≤ (1-R)/4 := hsmall.trans (min_le_left _ _)
  have hd1 : δ ≤ 1/100 := hsmall.trans (min_le_right _ _)
  refine ⟨Inverse.inverseRectSource_native canonicalFamily ?_, ?_⟩
  · constructor <;> simp only [anchorRect] <;> linarith
  · obtain ⟨B,L,c,hsrc,hL0,hL,hB,hc⟩ := hres δ hδ
    apply ordinaryRectSource_of_global hsrc hL0
    · simp only [anchorRect]
      have hS0 : 0 ≤ (1-R)/2+0-δ := by linarith
      have hS1 : (1-R)/2+0-δ ≤ 3/20 := by linarith
      have hLS := mul_le_mul_of_nonneg_right hL hS0
      have hδS := mul_le_mul_of_nonneg_left hS1 hδ.le
      nlinarith
    · simp only [anchorRect]
      linarith

/-- Unconditional supplier under the inherited beta case split. -/
theorem native_seed (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    {R : ℝ} (hR : 7/10 ≤ R) (hR1 : R < 1) : AnchorAt R 0 :=
  native_seed_of_reserve (Reserve.reserveParametricSource hβ) hR hR1

end Qrh.TwoSlot.AnchorContinuum
#print axioms Qrh.TwoSlot.AnchorContinuum.native_seed
