/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Reserve.Source
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.NativeBridge
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.Bridge

/-!
# Reserve.TopAnchors

The native anchors above the top of the stage chain and the bridge in the form consumed by the
driver (`Driver.improvedFiber_of_obligations`).

* `base_anchor_native`: the base anchor `(311/400, 0)` under `51/100 ≤ β` only.
* `top_anchors`: for `r ∈ [topEnd, topEnd + 1/1000]` the anchor `(r, g0 - g1 r)` on the count line.
  Here `z = g0 - g1 r ≤ -9/10000 < 0`, so every rectangle `anchorRect r z δ` is native for the
  inverse (`Pmax + 2 Smax = 1 + 2z - 3δ < 1`, `2 Pmax + 8 Smax = 4 - 2r + 8z - 10δ < 3`) and is
  covered by `G(B, L, c)` with `B ≥ 1-δ`, `L ≤ 2+δ`, `c ≥ 3/20-δ` from `reserveParametricSource`.
* `fiber_of_stages`: the stage anchors on `[leftEnd, topEnd]` give `ImprovedFiberMoments`
  (`Bridge.fiber_of_improved_split` with `hi = topEnd + 1/1000`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Reserve
noncomputable section

open OAI.SevenEighths
open Qrh.MarkedAnchor.Interface.Contract

/-- The base anchor `(311/400, 0)` of the stage chain, under `51/100 ≤ β` only. -/
theorem base_anchor_native (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) : AnchorAt (311/400) 0 :=
  Inverse.base_anchor_of_reserve (reserveParametricSource hβ)

/-- The native anchors on the count line just above the top `311/400`. -/
theorem top_anchors (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ImprovedMoments topEnd (topEnd + 1/1000) lineG0 lineG1 := by
  intro r hr1 hr2
  have hz : lineG0 - lineG1*r ≤ -9/10000 := by
    unfold lineG0 lineG1
    unfold topEnd at hr1
    linarith
  have hz' : -2/1000 ≤ lineG0 - lineG1*r := by
    unfold lineG0 lineG1
    unfold topEnd at hr2
    linarith
  have hr1' : 311/400 ≤ r := by simpa [topEnd] using hr1
  have hr2' : r ≤ 311/400 + 1/1000 := by simpa [topEnd] using hr2
  apply AnchorAt.of_small (δ₀ := 1/100) (by norm_num)
  intro δ hδ hδ1
  refine ⟨Inverse.inverseRectSource_native canonicalFamily ?_, ?_⟩
  · constructor <;> simp only [anchorRect] <;> linarith
  · obtain ⟨B,L,c,hsrc,hL0,hL,hB,hc⟩ := reserveParametricSource hβ δ hδ
    apply ordinaryRectSource_of_global hsrc hL0
    · simp only [anchorRect]
      have hS0 : 0 ≤ (1-r)/2+(lineG0-lineG1*r)-δ := by linarith
      have hS1 : (1-r)/2+(lineG0-lineG1*r)-δ ≤ 1/8 := by linarith
      have h1 := mul_le_mul_of_nonneg_right hL hS0
      have h2 := mul_le_mul_of_nonneg_left hS1 hδ.le
      nlinarith
    · simp only [anchorRect]
      linarith

/-- The bridge as the driver consumes it (`Driver.improvedFiber_of_obligations`): the stage
anchors on `[leftEnd, topEnd]` give the improved fiber moments of the return. -/
theorem fiber_of_stages (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hstages : ImprovedMoments leftEnd topEnd lineG0 lineG1) :
    Interface.ImprovedFiberMoments :=
  Interface.Bridge.fiber_of_improved_split (hi := topEnd + 1/1000)
    (by norm_num [Interface.anchorTop, topEnd]) hstages (top_anchors hβ)

/-- The same, in the shape of `Return.dirichlet_of_improved`'s hypothesis. -/
theorem fiber_of_stages_imp
    (hstages : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      ImprovedMoments leftEnd topEnd lineG0 lineG1) :
    (51/100:ℝ) ≤ HeckeZeroSupremum.beta → Interface.ImprovedFiberMoments :=
  fun hβ => fiber_of_stages hβ (hstages hβ)

end
end Qrh.MarkedAnchor.Reserve

#print axioms Qrh.MarkedAnchor.Reserve.base_anchor_native
#print axioms Qrh.MarkedAnchor.Reserve.top_anchors
#print axioms Qrh.MarkedAnchor.Reserve.fiber_of_stages
#print axioms Qrh.MarkedAnchor.Reserve.fiber_of_stages_imp
