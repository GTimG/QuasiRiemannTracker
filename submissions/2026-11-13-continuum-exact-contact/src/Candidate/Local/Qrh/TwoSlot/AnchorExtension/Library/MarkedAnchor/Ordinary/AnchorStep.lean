/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
The ordinary half of one anchor of the marked-anchor induction: the forked cube-free step at
`L = 0`.

`anchor_ordinary_step` proves `GlobalSource D.B D.L D.c` for the forked step data
(`AStepData`, with the reference width `lref`, the exceptional parameter `alpha` and the
high-root threshold `Pref`), from the forked step gates (`AStepGates`: no `1 < L`; the
reference gates of `ReferenceAt`), the reference lane (the hypothesis `ReferenceLaneFine D` of
`Reference/Statement.lean`, supplied by `Reference.reference_lane_fine` under the lane gates),
the contrary hypothesis, the parent source and the Seam A leaf. The root chain of
sil-density-split (restoration, packets, K3 kernels, second divisor, diagonal and label budgets,
the geometric supplier) is used unchanged through the fork; the only further scalar input is
`AStepInputs`: the leaf's plain-length cap `4 ≤ Lplain`. For the ordinary anchors `D.B = r`, `D.L = 0`, `D.c = S_new`, and
`GlobalSource r 0 S_new` is the rectangle `P ≤ r M`, `s ≤ S_new M`. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Assembly.Provider
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderDiag9
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderGeoSupply
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Reference.Statement

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary
noncomputable section
open OAI.SevenEighths QRH.Record1252270103Source QRH.SilDensitySplit.CubeFree
open Qrh.MarkedAnchor.Ordinary.Reference

/-- Step data of an ordinary anchor step (the forked cube-free step data). -/
abbrev AStepData := StepData

/-- Step gates of an ordinary anchor step (the forked gates: `0 ≤ L`, reference gates). -/
abbrev AStepGates (D : AStepData) := StepGates D

/-- The scalar input of one anchor step besides the reference lane: the plain
length cap of the Seam A leaf (the root chain needs `4 ≤ Lplain`, as in sil-density-split). -/
structure AStepInputs (D : AStepData) (G : AStepGates D) (Lplain : ℝ) : Prop where
  plain : 4 ≤ Lplain

/-- The root chain's restricted source (`StepInputs`) from the reference lane, through the
forked raw-side provider and diagonal supplier. -/
theorem stepInputs_of_reference (D : AStepData) (G : AStepGates D) (Lplain : ℝ)
    (I : AStepInputs D G Lplain) (href : ReferenceLaneFine D) : StepInputs D G Lplain :=
  Assembly.step_inputs_of_provider D G Lplain href (fun _ hleaf =>
    Second.Provider.contrary_raw_side_provider G Lplain I.plain hleaf
      (Second.ProviderDiag.diag_supply G))

/-- **The ordinary anchor step** (valid for `D.L = 0`). -/
theorem anchor_ordinary_step (D : AStepData) (G : AStepGates D) (Lplain : ℝ)
    (I : AStepInputs D G Lplain) (href : ReferenceLaneFine D)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : GlobalSource D.B₀ D.L₀ D.c₀)
    (hleaf : PricedPackedSource D.price D.Hmin (D.Hmax+1) Lplain) :
    GlobalSource D.B D.L D.c :=
  cubefree_step D G Lplain (stepInputs_of_reference D G Lplain I href) hβ hparent hleaf

/-- The same with the leaf at `Lplain = 4`. -/
theorem anchor_ordinary_step_four (D : AStepData) (G : AStepGates D) (href : ReferenceLaneFine D)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : GlobalSource D.B₀ D.L₀ D.c₀)
    (hleaf : PricedPackedSource D.price D.Hmin (D.Hmax+1) 4) :
    GlobalSource D.B D.L D.c :=
  anchor_ordinary_step D G 4 ⟨le_rfl⟩ href hβ hparent hleaf

/-- The reference parameters of the ordinary anchors, `l_ref = 7/50`, `alpha = 3/5` (with the
threshold `Pref = 2/3`), satisfy the parameter part of `ReferenceAt`. -/
theorem reference_parameters_P :
    (0:ℝ) < 7/50 ∧ 2*(7/50:ℝ) < 2/3 ∧ (0:ℝ) < 3/5 ∧ (3/5:ℝ) < 2/3 := by norm_num

end
end Qrh.MarkedAnchor.Ordinary
