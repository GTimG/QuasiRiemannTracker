/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Inverse.Contract
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Inverse.Ledger

/-!
# High.Inverse.Stage — the HIGH input of the inverse child at every chain point

* `inverse_high_stage_of_priced` — for ANY slot family: the priced HIGH energy at the floor
  `R n + 10^-6` gives `InverseHighEnergy fam (chainChildRect n r β κ) (cut n) (chainExcess n r κ)`
  (scalar ledger `chain_child_price_le`; the radius shift `κ ≤ β/8` is absorbed by the
  `β`-decrement of the free width).
* `inverse_high_stage` — the HIGH input for `canonicalFamily` (fixed ray data) from the detector
  leaf `InverseHighLeaf` (a hypothesis here, supplied by `inverseHighLeaf`) and the marked inputs
  `HighMarkedInverseCoreInputs (a0 n) (a1 n) (R n + 10^-6)` (from `EarlierAnchors n`).
* `inverse_child_stage` — the whole inverse child of the stage (LOW + HIGH).

`canonicalFamily` is the fixed-ray family of `Interface.Contract`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Inverse
noncomputable section

open OAI OAI.SevenEighths
open Qrh.MarkedAnchor.High
open Qrh.MarkedAnchor.Anchor ChainData ChainCheck
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Inverse.Leaf

/-- **The priced HIGH energy gives the HIGH input of the inverse child of stage `n`.** -/
theorem inverse_high_stage_of_priced (fam : SlotClass → Prop) (n : ℕ) (hn : n < 176) (r : ℝ)
    (h1 : (left n : ℝ) ≤ r) (h2 : r ≤ R n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1/1000) (κ : ℝ)
    (hκ : 0 < κ ∧ κ ≤ β/8)
    (hP : InverseHighPriced fam (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000)) :
    InverseHighEnergy fam (chainChildRect n r β κ) (cut n) (chainExcess n r κ) := by
  obtain ⟨hκ0, hκ1⟩ := hκ
  have hS0 := Qrh.MarkedAnchor.Price.stageHyp_chain n hn r h1 h2
  have hu1 := hS0.hu
  have hu0 := hS0.u_nonneg
  have hR1 := hS0.hR.2
  intro ε hε
  obtain ⟨mesh, hmesh, h⟩ := hP ε hε
  refine ⟨mesh, hmesh, fun K lam hlam cls hcls Φ ao bo hao hab hΦs hΦ data => ?_⟩
  obtain ⟨degree, c, C, Z₀, hc, hC, hZ₀, hb⟩ := h K lam hlam cls hcls Φ ao bo hao hab hΦs hΦ data
  refine ⟨degree, c, C, Z₀, hc, hC, hZ₀, fun Z hZ => ?_⟩
  intro ι _ _ hK L ell bc hv hv0 hcl g1 g2 g3 g4 g5 g6 r' hadm rows hrows θ
  have hle := chain_child_price_le n hn r h1 h2 β hβ0 hβ1 κ hκ0 hκ1 r' (∑ i, ell i) hadm
  have hr'1 : r' ≤ 1 := by
    have hr' := hadm.2.1
    simp only [chainChildRect, Qrh.MarkedAnchor.Inverse.childRect, mul_one] at hr'
    have hpos : 0 < 1 - 6*fu (R n : ℝ) r - κ := by linarith
    have : (r - β + 2*κ)/(1 - 6*fu (R n : ℝ) r - κ) ≤ 1 := by
      rw [div_le_one hpos]; linarith
    linarith
  refine (hb Z hZ hK L ell bc hv hv0 hcl g1 g2 g3 g4 g5 g6 r' hadm.1 hr'1 rows hrows θ).trans ?_
  have hZ1 : 1 ≤ Z := hZ₀.le.trans hZ
  have hpos : 0 ≤ ((1+‖θ‖+hv)^degree)^2 := by positivity
  apply mul_le_mul_of_nonneg_right _ hpos
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)) hC.le

/-- **The HIGH input of the inverse child of stage `n`** (`canonicalFamily`, fixed ray data), from the
detector leaf and the marked inputs at the floor `R n + 10^-6`. -/
theorem inverse_high_stage (hleaf : InverseHighLeaf)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) (n : ℕ) (hn : n < 176) (r : ℝ)
    (h1 : (left n : ℝ) ≤ r) (h2 : r ≤ R n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1/1000) (κ : ℝ)
    (hκ : 0 < κ ∧ κ ≤ β/8)
    (hm : HighMarkedInverseCoreInputs (a0 n) (a1 n) ((R n : ℝ) + 1/1000000)) :
    InverseHighEnergy canonicalFamily (chainChildRect n r β κ) (cut n) (chainExcess n r κ) := by
  have h := chain_hyp n hn r h1 h2
  have hk := chain_cut_mem n hn
  exact inverse_high_stage_of_priced canonicalFamily n hn r h1 h2 β hβ0 hβ1 κ hκ
    (hleaf (a0 n) (a1 n) (cut n) _ hβ hk.1 hk.2 h.a1_nonneg (h.a1_le.trans (by norm_num))
      (chain_floor_le n hn) hm)

/-- **The HIGH input of the inverse child of stage `n` from the earlier anchors** (with the leaf
`hleaf` and the reserve source `hres` used for the plain cores). -/
theorem inverse_high_stage_of_anchors (hleaf : InverseHighLeaf)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hres : Qrh.MarkedAnchor.Interface.Native.ReserveParametricSource) (n : ℕ) (hn : n < 176)
    (r : ℝ) (h1 : (left n : ℝ) ≤ r) (h2 : r ≤ R n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1/1000)
    (κ : ℝ) (hκ : 0 < κ ∧ κ ≤ β/8) (hE : EarlierAnchors n) :
    InverseHighEnergy canonicalFamily (chainChildRect n r β κ) (cut n) (chainExcess n r κ) :=
  inverse_high_stage hleaf hβ n hn r h1 h2 β hβ0 hβ1 κ hκ
    (highMarkedInverseCoreInputs_stage hβ hres n hn hE)

/-- **The inverse child of stage `n`** (LOW from the previous anchor, HIGH from the leaf), for the
canonical family, with excess `u/(1-6u-κ)`. -/
theorem inverse_child_stage (hleaf : InverseHighLeaf)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) (n : ℕ) (hn : n < 176) (r : ℝ)
    (h1 : (left n : ℝ) ≤ r) (h2 : r ≤ R n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1/1000) (κ : ℝ)
    (hκ : 0 < κ ∧ κ ≤ β/8) (hA : AnchorAt (R n) (gain n))
    (hm : HighMarkedInverseCoreInputs (a0 n) (a1 n) ((R n : ℝ) + 1/1000000)) :
    UniformInverseRectSourceExcess canonicalFamily (chainChildRect n r β κ)
      (chainExcess n r κ) :=
  chain_inverse_child_of_anchor n hn r h1 h2 β hβ0 hβ1 κ hκ.1 hκ.2 hA
    (inverse_high_stage hleaf hβ n hn r h1 h2 β hβ0 hβ1 κ hκ hm)

end
end Qrh.MarkedAnchor.High.Inverse

#print axioms Qrh.MarkedAnchor.High.Inverse.inverse_high_stage_of_priced
#print axioms Qrh.MarkedAnchor.High.Inverse.inverse_high_stage
#print axioms Qrh.MarkedAnchor.High.Inverse.inverse_child_stage
#print axioms Qrh.MarkedAnchor.High.Inverse.inverse_high_stage_of_anchors
