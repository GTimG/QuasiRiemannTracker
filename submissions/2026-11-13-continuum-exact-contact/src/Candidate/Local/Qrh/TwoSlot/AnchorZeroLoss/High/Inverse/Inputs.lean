/- Modified by Joseph Bebel (2026-11-12): smaller-tolerance inverse
HIGH leaf; original coefficient, mask and principal-row proofs are retained. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.LeafMarkedInput
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Marked.Contract

/-!
# Paired core-form inputs for the inverse HIGH leaf

The physical cofactor classes use both fields of `MarkedCoreR1`, with the
original core character, canonical slots, bounded common profiles and heights.
The raw-row inverse field of the preceding interface was unused and is absent
from this contract. Fixed-inducing rows retain their separate native estimate.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Inverse
noncomputable section
variable [shift : WitnessShift]
open Qrh.TwoSlot.AnchorZeroLoss.High

/-- `MarkedCoreR1` (proved per stage) gives the bounded-height core inputs of the leaf. -/
theorem highMarkedCoreInputsH_of_R1 {a0 a1 wlo : ℝ} (h : Marked.MarkedCoreR1 a0 a1 wlo (1/10000000000000) WitnessShift.value) :
    HighMarkedCoreInputsH a0 a1 wlo (1/10000000000000) WitnessShift.value := by
  intro εm hεm
  obtain ⟨meshm, hm, h'⟩ := h εm hεm
  refine ⟨meshm, hm, ?_⟩
  intro rayM _ H hH W hWs hW η η₀ Slot _ _ wrmin hwrmin
  obtain ⟨J, C, hC, hev⟩ := h' rayM H hH W hWs hW η η₀ (Slot := Slot) wrmin hwrmin
  refine ⟨J, C, hC, hev.mono fun U hU => ⟨hU.1, ?_⟩⟩
  intro a ε Tz allowance height i _ _ _ hh _ slots θ wr σ v t hwmin hwm hσ hv rows hnorm
    hreg ht wc hwc hwlo _ label J' K' _ C' hC'
  exact hU.2 height hh slots θ wr σ v t hwmin hwm hσ hv rows hnorm hreg ht wc hwc hwlo
    label J' K' C' hC'

/-- The paired core-form source supplies the inverse leaf's bounded-height inputs. -/
theorem highMarkedCoreInputsH_of_inverse {a0 a1 wlo : ℝ}
    (h : Marked.MarkedCoreR1 a0 a1 wlo (1/10000000000000) WitnessShift.value) : HighMarkedCoreInputsH a0 a1 wlo (1/10000000000000) WitnessShift.value :=
  highMarkedCoreInputsH_of_R1 h

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Inverse

#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.highMarkedCoreInputsH_of_R1
