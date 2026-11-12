/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafMarkedInput
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Marked.Contract

/-!
# High.Inverse.Inputs — the core-form marked inputs of the inverse HIGH leaf

The inverse detector takes BOTH marked fields in core form on the cofactor cores. The second
conjunct `Marked.MarkedCoreR1` of `HighMarkedInverseCoreInputs` carries the core-form INVERSE field
(`Marked.InvMarkedField`: `coreFamily`, `coreSlot`, every `η η₀`) next to the plain one, and it is
proved per stage (`markedCoreR1_stage`). The inverse rows enter it through
* `H := G.pool`, `η := dataBase data` (`High.Inverse.Dictionary`: `data.character w` is the natural
  row of `w` for this base, with the same zero maxima as the clean core family),
* `η₀ := dataBase data · rayChar(θ)⁻¹` (the common relative twist), core slot twists `1`.

`highMarkedCoreInputsH_of_R1` converts `MarkedCoreR1` to the consumer form `HighMarkedCoreInputsH`
of the per-class core batch lemma `High.core_class_batch` (LeafClass), which is generic in the
row energy (`rowsq`) and the raw slot norms (`ns`), hence usable verbatim for inverse rows.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Inverse
noncomputable section
open Qrh.MarkedAnchor.High

/-- `MarkedCoreR1` (proved per stage) gives the bounded-height core inputs of the leaf. -/
theorem highMarkedCoreInputsH_of_R1 {a0 a1 wlo : ℝ} (h : Marked.MarkedCoreR1 a0 a1 wlo) :
    HighMarkedCoreInputsH a0 a1 wlo := by
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

/-- The core inputs of the inverse leaf from the second conjunct of `HighMarkedInverseCoreInputs`
(`= HighMarkedInverseInvField ∧ MarkedCoreR1`; the first conjunct is unused). -/
theorem highMarkedCoreInputsH_of_inverse {a0 a1 wlo : ℝ} {Pinv : Prop}
    (h : Pinv ∧ Marked.MarkedCoreR1 a0 a1 wlo) :
    HighMarkedCoreInputsH a0 a1 wlo :=
  highMarkedCoreInputsH_of_R1 h.2

end
end Qrh.MarkedAnchor.High.Inverse

#print axioms Qrh.MarkedAnchor.High.Inverse.highMarkedCoreInputsH_of_R1
