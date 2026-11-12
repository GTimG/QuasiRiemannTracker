/- Copyright (c) 2026 Sil. Apache-2.0.
The generic cube-free common-divisor step.

`StepInputs D G Lplain` is the analytic input of one step: the top output of the root chain
(Seam 0, the diagonal budget, the label budget and the root data), namely the restricted
cube-free source on all roots of width `≥ s₀`, from `51/100 ≤ β`, the parent source and the
Seam A leaf at the envelope `[Hmin, Hmax+1]`. `cubefree_step` adds the inherited roots
(`∑ w < s₀`, CF crossing), the per-T restoration and the merging of constants.
Modified by Sil (2026-11-11): fork for the ordinary anchors, namespace
`Qrh.MarkedAnchor.Ordinary`: only the generic step is kept (the native and density instances
and their leaves are not forked); `0 ≤ L` comes from the forked `StepGates.face`. -/
import Submissions.sil_density_split_20261026.CubeFree.Assembly.Combine
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.StepData
import Submissions.sil_density_split_20261026.CubeFree.Leaf.Contract

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree
noncomputable section
open OAI.SevenEighths QRH.Record1252270103Source QRH.SilDensitySplit.CubeFree.Assembly

/-- The analytic input of one cube-free step (the root chain's top statement). -/
structure StepInputs (D : StepData) (G : StepGates D) (Lplain : ℝ) : Prop where
  restricted : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
    GlobalSource D.B₀ D.L₀ D.c₀ →
    PricedPackedSource D.price D.Hmin (D.Hmax+1) Lplain →
    HighRestrictedUnitSource (globalFace D.B D.L D.c) D.s₀

/-- **The generic cube-free step.** -/
theorem cubefree_step (D : StepData) (G : StepGates D) (Lplain : ℝ) (I : StepInputs D G Lplain)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : GlobalSource D.B₀ D.L₀ D.c₀)
    (hleaf : PricedPackedSource D.price D.Hmin (D.Hmax+1) Lplain) :
    GlobalSource D.B D.L D.c := by
  obtain ⟨hB, hB₀, hLL, hL0, -⟩ := G.face
  exact global_source_of_parent_and_high D.B D.L D.c D.B₀ D.L₀ D.c₀ D.s₀ (by linarith)
    (by linarith) (by linarith) (fun P S hS0 hS hroot => G.inherit hS0 hS hroot) hparent
    (I.restricted hβ hparent hleaf)

end
end Qrh.MarkedAnchor.Ordinary
