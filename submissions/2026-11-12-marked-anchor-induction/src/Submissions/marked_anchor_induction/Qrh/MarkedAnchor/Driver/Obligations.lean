/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Price.Stage
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Sources
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafContract
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafMarkedInput
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafStage
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Marked.Stage
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Inverse.Stage
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Select.Stage
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Reduction
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Init.DirectEnergy
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Inverse.Leaf
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Reference.Lane

/-!
# Driver.Obligations

End-to-end assembly of the anchor induction over the 176 stages, with the restoration of the
selection child as the single field of `Obligations` (it is supplied by `Driver.obligations` in
`Driver.Unconditional`).

* `Obligations` — the restoration hypothesis consumed by the inverse half of each stage.
* `chainHighLedger` — the stage ledger `Price.ChainHighLedger` of the floored price
  (`High.chain_highPriceW_le`).
* `laneGates_stage`, `reference_stage` — the reference lane at every stage point
  (`Ordinary.Reference.reference_lane_fine`, gates with `ρ = 1/100` from `stageHyp_chain`).
* `gain_succ_le`, `prev_anchor` — the entry anchor `(R n, gain n)` of stage `n`: the base anchor
  for `n = 0`, stage `n-1` at its left end (`AnchorAt.mono` and the downward rounding of
  `gain (n+1)`) for `n ≥ 1`.
* `ordinary_high_stage` — the ordinary HIGH rows of stage `n` from the leaf
  `High.ordinary_high_leaf` and `High.Marked.highMarkedCoreInputsR1_stage`.
* `stage_point` — one stage point: ordinary half `Price.chain_ordinary_anchor`; inverse half
  `Inverse.Inj.inverse_reduction_excess_canonical_stage` (injective oracle chain
  `Inverse.Inj.oracleChain_canonical`; selection `Inverse.selectionReductionExcessInj_canonical`)
  with the child `Inverse.Leaf.chain_inverse_child_of_anchor` (LOW: entry anchor; HIGH:
  `High.Inverse.inverse_high_stage_of_anchors` with the leaf `High.Inverse.inverseHighLeaf`),
  slack `κ = β/8`.
* `all_stages` — the induction over the 176 stages (strong induction; stage `n` uses only
  `High.EarlierAnchors n`).
* `improved_of_obligations` — `Contract.ImprovedMoments leftEnd topEnd lineG0 lineG1` from
  `ChainCheck.return_line_minorant` and `Contract.improved_of_anchors`.

The parent source of the ordinary step (`pr103Face`), `ReserveParametricSource` and the base
anchor `(311/400, 0)` are parameters here; they are discharged in `Driver.Final` (`Driver.pr103_parent`,
`Reserve.base_anchor_native`), as is the bridge (`Reserve.fiber_of_stages`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Driver
noncomputable section

open OAI OAI.SevenEighths
open Qrh.MarkedAnchor.Anchor.ChainData Qrh.MarkedAnchor.Anchor.ChainCheck
open Qrh.MarkedAnchor.Interface.Contract
open Qrh.MarkedAnchor.Price (pr103Face stageData stageDelta cut_nonneg cut_le
  stageHyp_chain chain_ordinary_anchor)

/-- **The obligations** consumed by the assembly, premised on the contrary hypothesis
`51/100 ≤ β`; supplied by `Driver.obligations`. -/
structure Obligations : Prop where
  /-- The restoration of the selection child (`Inverse.RestoreChildBoundUniform`). -/
  restore : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
    Inverse.RestoreChildBoundUniform canonicalFamily canonicalFamily

/-- The stage ledger of the floored price. -/
theorem chainHighLedger : Price.ChainHighLedger := High.chain_highPriceW_le

/-- The scalar gates of the reference lane at every stage point (reserve `ρ = 1/100`;
`c ≤ S(r) < 137/1000` by gate 2). -/
theorem laneGates_stage (n : ℕ) (hn : n < 176) (r : ℝ) (h1 : (left n : ℝ) ≤ r) (h2 : r ≤ R n)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1/1000) :
    Ordinary.Reference.LaneGates (stageData pr103Face (R n) (gain n) (cut n) r β
      (High.highPriceW (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000) (cut_nonneg n hn)
        (cut_le n hn))
      (cut_nonneg n hn) hβ0) (1/100) := by
  have hS := stageHyp_chain n hn r h1 h2
  have hc := Price.stage_c_eq pr103Face
    (High.highPriceW (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000) (cut_nonneg n hn)
        (cut_le n hn)) (cut_nonneg n hn)
    (r := r) (z := (gain n : ℝ)) (R := (R n : ℝ)) hβ0
  have hlref : (stageData pr103Face (R n) (gain n) (cut n) r β
      (High.highPriceW (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000) (cut_nonneg n hn)
        (cut_le n hn))
      (cut_nonneg n hn) hβ0).lref = 7/50 := rfl
  have hdd : stageDelta = 1 / 25000000 := rfl
  have g2 := hS.g2
  have hSl := hS.S_lower
  have hr2 := hS.hr.2
  have hR2 := hS.hR.2
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlref]; norm_num
  · rw [hc, hdd]; linarith
  · rw [hlref, hc, hdd]
    simp only [Ordinary.Reference.Lref, Ordinary.Reference.Bref]
    linarith
  · rw [hc, hdd]; simp only [Ordinary.Reference.cref]; linarith
  · rw [hlref, hc, hdd]; linarith

/-- The reference lane at every stage point (`Ordinary.Reference.reference_lane_fine`). -/
theorem reference_stage (n : ℕ) (hn : n < 176) (r : ℝ) (h1 : (left n : ℝ) ≤ r) (h2 : r ≤ R n) :
    ∀ β : ℝ, ∀ hβ0 : 0 < β, β ≤ 1/1000 →
      Ordinary.Reference.ReferenceLaneFine (stageData pr103Face (R n) (gain n) (cut n) r β
        (High.highPriceW (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000) (cut_nonneg n hn)
        (cut_le n hn))
        (cut_nonneg n hn) hβ0) :=
  fun β hβ0 hβ1 => Ordinary.Reference.reference_lane_fine (laneGates_stage n hn r h1 h2 β hβ0 hβ1)

/-- The anchors of stage `n` (the conclusion of one stage of the induction). -/
def StageAnchors (n : ℕ) : Prop :=
  ∀ r : ℝ, (left n : ℝ) ≤ r → r ≤ R n →
    AnchorAt r (fY (R n : ℝ) (gain n) (cut n) r - 1 / 25000000)

/-- The entry gain of stage `m+1` (rounded down) is below the gain of stage `m` at its left end. -/
theorem gain_succ_le (m : ℕ) :
    (gain (m+1) : ℝ) ≤ fY (R m : ℝ) (gain m) (cut m) (left m) - 1 / 25000000 := by
  have hq : gain (m+1) ≤ (stage m).Y (left m) - DELTA := by
    rw [gain_succ_eq, div_le_iff₀ (by norm_num)]
    exact Int.floor_le _
  have e : ((((stage m).Y (left m) - DELTA : ℚ)) : ℝ) =
      fY (R m : ℝ) (gain m) (cut m) (left m) - 1 / 25000000 := by
    simp only [Stage.Y, fY, fu, DELTA]; push_cast; ring
  rw [← e]
  exact_mod_cast hq

/-- The entry anchor `(R n, gain n)` of stage `n`. -/
theorem prev_anchor (base : AnchorAt (311/400) 0) (n : ℕ) (IH : High.EarlierAnchors n) :
    AnchorAt (R n) (gain n) := by
  rcases n with _ | m
  · have e1 : ((R 0 : ℚ) : ℝ) = 311/400 := by rw [R_eq]; norm_num
    have e2 : ((gain 0 : ℚ) : ℝ) = 0 := by rw [gain_zero]; norm_num
    rw [e1, e2]
    exact base
  · have hA := IH m (Nat.lt_succ_self m) (left m) le_rfl (left_lt_R m).le
    have e : ((R (m+1) : ℚ) : ℝ) = ((left m : ℚ) : ℝ) := rfl
    refine hA.mono (le_of_eq e) ?_
    rw [e]
    linarith [gain_succ_le m]

/-- The ordinary HIGH rows of stage `n` (leaf `High.ordinary_high_leaf`, inputs
`High.Marked.highMarkedCoreInputsR1_stage` from the earlier anchors). -/
theorem ordinary_high_stage (O : Obligations) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hres : Interface.Native.ReserveParametricSource) (n : ℕ) (hn : n < 176)
    (IH : High.EarlierAnchors n) (r : ℝ) (h1 : (left n : ℝ) ≤ r) (h2 : r ≤ R n) :
    High.HighBranchMesh (High.highPriceW (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000)
      (cut_nonneg n hn) (cut_le n hn)) (cut n) := by
  have h := High.chain_hyp n hn r h1 h2
  have hk := High.chain_cut_mem n hn
  exact High.ordinary_high_leaf (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000) (cut_nonneg n hn)
    (cut_le n hn) hβ hk.1 (High.chain_floor_le n hn) h.a1_nonneg (h.a1_le.trans (by norm_num))
    (High.Marked.highMarkedCoreInputsR1_stage hβ hres n hn IH)

/-- **One stage point.** Both halves of `AnchorAt r (Y_n(r) - δ)` for `r ∈ [left n, R n]`. -/
theorem stage_point (O : Obligations) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hres : Interface.Native.ReserveParametricSource)
    (hparent : QRH.Record1252270103Source.GlobalSource pr103Face.B₀ pr103Face.L₀ pr103Face.c₀)
    (n : ℕ) (hn : n < 176) (IH : High.EarlierAnchors n) (prev : AnchorAt (R n) (gain n))
    (r : ℝ) (h1 : (left n : ℝ) ≤ r) (h2 : r ≤ R n) :
    AnchorAt r (fY (R n : ℝ) (gain n) (cut n) r - 1 / 25000000) := by
  have hS := stageHyp_chain n hn r h1 h2
  have hord := chain_ordinary_anchor pr103Face chainHighLedger n hn r h1 h2
    (reference_stage n hn r h1 h2) hβ hparent (fun δ' hδ' => (prev δ' hδ').2)
    (ordinary_high_stage O hβ hres n hn IH r h1 h2)
  have hdd : stageDelta = 1 / 25000000 := rfl
  rw [hdd] at hord
  refine AnchorAt.of_small (δ₀ := 1/1000) (by norm_num) (fun β hβ0 hβ1 => ⟨?_, hord β hβ0⟩)
  have hκ : 0 < β/8 ∧ β/8 ≤ β/8 := ⟨by linarith, le_rfl⟩
  -- the inverse child: LOW from the entry anchor, HIGH from the inverse leaf (earlier anchors)
  have hchild := Inverse.Leaf.chain_inverse_child_of_anchor n hn r h1 h2 β hβ0 hβ1 (β/8) hκ.1
    le_rfl prev
    (High.Inverse.inverse_high_stage_of_anchors High.Inverse.inverseHighLeaf hβ hres n hn r h1 h2 β hβ0 hβ1
      (β/8) hκ IH)
  have hH1 := hS.H_le_one
  have hH0 := hS.H_ge
  have hY := hS.Y_nonneg
  have g4 := hS.g4
  have hu : (1 - fH (R n : ℝ) r)/6 = fu (R n : ℝ) r := by unfold fH fu; ring
  have hfS : fS (R n : ℝ) (gain n) (cut n) r = (1-r)/2 + fY (R n : ℝ) (gain n) (cut n) r := rfl
  have hchild' : Inverse.Leaf.UniformInverseRectSourceExcess canonicalFamily
      (Inverse.childRect (r - β) ((1-r)/2 + (fY (R n : ℝ) (gain n) (cut n) r - 1 / 25000000) - β)
        ((1 - fH (R n : ℝ) r)/6) (β/8))
      (((1 - fH (R n : ℝ) r)/6)/(1-6*((1 - fH (R n : ℝ) r)/6)-β/8)) := by
    rw [hu]; exact hchild
  exact Inverse.Inj.inverse_reduction_excess_canonical_stage Inverse.Inj.oracleChain_canonical
    (Inverse.selectionReductionExcessInj_canonical (O.restore hβ))
    (fH (R n : ℝ) r) (r - β)
    ((1-r)/2 + (fY (R n : ℝ) (gain n) (cut n) r - 1 / 25000000) - β) (β/8)
    (by linarith) hH1 (by linarith [hS.hr.1]) (by linarith [hS.hr.2, hS.hR.2])
    hκ.1 (by linarith) (by rw [hu]; linarith) hchild'

/-- **The induction over the 176 stages.** -/
theorem all_stages (O : Obligations) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hres : Interface.Native.ReserveParametricSource)
    (hparent : QRH.Record1252270103Source.GlobalSource pr103Face.B₀ pr103Face.L₀ pr103Face.c₀)
    (base : AnchorAt (311/400) 0) :
    ∀ n : ℕ, n < 176 → StageAnchors n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have IH : High.EarlierAnchors n := fun j hj => ih j hj (by omega)
    intro r h1 h2
    exact stage_point O hβ hres hparent n hn IH (prev_anchor base n IH) r h1 h2

/-- **The improved family on the return line** `(lineG0, lineG1)` over `[leftEnd, topEnd]`
(margin: the pad `10^-7` of `return_line_minorant`, unused beyond `≥`). -/
theorem improved_of_obligations (O : Obligations) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hres : Interface.Native.ReserveParametricSource)
    (hparent : QRH.Record1252270103Source.GlobalSource pr103Face.B₀ pr103Face.L₀ pr103Face.c₀)
    (base : AnchorAt (311/400) 0) :
    Interface.Contract.ImprovedMoments Interface.Contract.leftEnd Interface.Contract.topEnd
      Interface.Contract.lineG0 Interface.Contract.lineG1 := by
  have hall := all_stages O hβ hres hparent base
  apply improved_of_anchors
  intro r hlo hhi
  have hlo' : (1467/2000 : ℝ) ≤ r := hlo
  have hhi' : r ≤ 311/400 := hhi
  obtain ⟨j, hj, h1, h2, hpos⟩ := return_line_minorant r ⟨hlo', hhi'⟩
  refine ⟨r, fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000, hall j hj r h1 h2, le_rfl, ?_⟩
  simp only [fline] at hpos
  simp only [Interface.Contract.lineG0, Interface.Contract.lineG1]
  linarith

end
end Qrh.MarkedAnchor.Driver

#print axioms Qrh.MarkedAnchor.Driver.all_stages
#print axioms Qrh.MarkedAnchor.Driver.improved_of_obligations
