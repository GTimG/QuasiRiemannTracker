/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.Native
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionInverse

/-!
# Inverse.NativeBridge

`NativeDirectInverse` (`Interface.Native`) holds. It is HC's
`direct_reference_energy` in its prebuilt copy
`Record1252270103Bootstrap/PR67Source/Cycle63/Marked/DeletionInverse.lean` (same statement as
`Record12518109Gain/Upstream/DeletionInverse.lean:172`); `directPrimeSlot` there is
definitionally `Contract.directSlot`.

Consequences: the native inverse contract on every native rectangle and the base anchor need only
the ordinary premise `ReserveParametricSource`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open DetectorDictionaryInverseRawInitialGates
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
local notation "O" => HeckeFamily.O

theorem directSlot_eq_directPrimeSlot (u : O) (L : Finset (Ideal O)) (β : Ideal O → ℂ) (P : ℝ) :
    directSlot u L β P =
      Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.directPrimeSlot u L β P := rfl

/-- The native direct inverse marked estimate (HC `direct_reference_energy`). -/
theorem nativeDirectInverse : NativeDirectInverse := by
  intro W ao bo hao hab hsW hW εm hεm K
  exact Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.direct_reference_energy
    W ao bo hao hab hsW hW εm hεm K

/-- The native inverse contract on every rectangle of the native region, unconditionally. -/
theorem inverseRectSource_native (fam : SlotClass → Prop) {ρ : AnchorRect}
    (hρ : ρ.NativeInverse) : UniformInverseRectSource fam ρ :=
  inverseRectSource_of_native nativeDirectInverse fam hρ

/-- The base anchor needs only the ordinary reserve-parametric premise. -/
theorem base_anchor_of_reserve (hres : ReserveParametricSource) : AnchorAt (311/400) 0 :=
  base_anchor nativeDirectInverse hres

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.nativeDirectInverse
#print axioms Qrh.MarkedAnchor.Inverse.base_anchor_of_reserve
