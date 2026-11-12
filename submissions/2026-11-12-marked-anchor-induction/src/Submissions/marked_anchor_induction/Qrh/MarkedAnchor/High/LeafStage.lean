/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafBranch
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Marked.Stage
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Gates

/-!
# High.LeafStage

The ordinary HIGH leaf per stage.

* `ordinary_high_leaf` — `High.LeafBranch.high_branch_mesh` in the form used by
  `Driver.ordinary_high_stage`.
* `highMarkedCoreInputsH_of_R1` — `Marked.HighMarkedCoreInputsR1` is the leaf's
  `HighMarkedCoreInputsH` (definitional: its named fields unfold to the verbatim ones).
* `high_stage` — `HighBranchMesh (highPriceW (a0 n) (a1 n) (cut n) (R n + 10^-6) …) (cut n)` for every
  stage `n < 176`, from `β ≥ 51/100`, the reserve-parametric source and the earlier anchors
  (`Marked.highMarkedCoreInputsR1_stage`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open OAI OAI.SevenEighths
open Qrh.MarkedAnchor.Anchor ChainData ChainCheck
open Qrh.MarkedAnchor.Interface.Native

/-- **The ordinary HIGH leaf in the form used by `Driver.ordinary_high_stage`.** -/
theorem ordinary_high_leaf : ∀ (a0 a1 k wlo : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 3/4),
    (51/100:ℝ) ≤ HeckeZeroSupremum.beta → 1/6 ≤ k → wlo ≤ cutHi → 0 ≤ a1 → a1 ≤ 1/2 →
    HighMarkedCoreInputsH a0 a1 wlo →
    HighBranchMesh (highPriceW a0 a1 k wlo hk0 hk1) k :=
  fun _ _ _ _ _ hk1 hβ hk hlo ha1 ha1' hM => high_branch_mesh hβ hk hk1 hlo ha1 ha1' hM

/-- The marked contract `Marked.HighMarkedCoreInputsR1` is the leaf's input. -/
theorem highMarkedCoreInputsH_of_R1 {a0 a1 wlo : ℝ}
    (h : Marked.HighMarkedCoreInputsR1 a0 a1 wlo) : HighMarkedCoreInputsH a0 a1 wlo := h

/-- **The ordinary HIGH leaf of stage `n`.** -/
theorem high_stage (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource) (n : ℕ) (hn : n < 176) (hE : EarlierAnchors n) :
    HighBranchMesh (highPriceW (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000)
      (by have := chain_cut_mem n hn; linarith) (chain_cut_mem n hn).2) (cut n) := by
  have hk := chain_cut_mem n hn
  have h := chain_hyp n hn (R n) (left_lt_R n).le le_rfl
  exact high_branch_mesh hβ hk.1 hk.2 (chain_floor_le n hn) h.a1_nonneg
    (h.a1_le.trans (by norm_num))
    (highMarkedCoreInputsH_of_R1 (Marked.highMarkedCoreInputsR1_stage hβ hres n hn hE))

end
end Qrh.MarkedAnchor.High

#print axioms Qrh.MarkedAnchor.High.high_branch_mesh
#print axioms Qrh.MarkedAnchor.High.high_stage
#print axioms Qrh.MarkedAnchor.High.ordinary_high_leaf
