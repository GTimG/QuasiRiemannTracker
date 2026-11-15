/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Price.Gates
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Price.Leaf
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.AnchorStep
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.Contract

/-!
# Price.Stage

The ordinary half of one anchor stage: the forked cube-free step
(`Ordinary.anchor_ordinary_step_four`) at the stage data `stageData`, with
* the gates `stageGates` (`Price.Gates`),
* the leaf `anchor_priced_source` (`Price.Leaf`) for the face `G(R-δ₁, β/4, S_R-δ₁)`, a
  restriction of the previous anchor (`globalSource_soft`), and the HIGH rows hypothesis.

`stage_anchor` (generic stage point) and `chain_ordinary_anchor` (the 256 stages, all decrements
`β > 0`): from the previous anchor's ordinary rectangle at `(R n, gain n)`, the parent face, the
reference lane (`Ordinary.Reference.ReferenceLaneFine`), the stage ledger of the HIGH price
(`ChainHighLedger`) and the HIGH rows (`High.HighBranchMesh`), the new ordinary rectangle
`anchorRect r (Y(r) - δ) β` for every `r ∈ [left n, R n]`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Price
noncomputable section
open OAI OAI.SevenEighths QRH.SilDensitySplit.CubeFree
open Qrh.TwoSlot.AnchorExtension.ChainData
open Qrh.TwoSlot.AnchorExtension.ChainCheck
open Qrh.MarkedAnchor.Interface.Contract (OrdinaryRectSource anchorRect anchorRect_restricts
  uniformUnitFaceSource_restrict)

/-- Raising the marked budget of a global face shrinks it: `G(B,0,c) ⇒ G(B,ℓ,c)` for `ℓ ≥ 0`. -/
theorem globalSource_soft {B c ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (h : QRH.Record1252270103Source.GlobalSource B 0 c) :
    QRH.Record1252270103Source.GlobalSource B ℓ c :=
  uniformUnitFaceSource_restrict (strong := QRH.Record1252270103Source.globalFace B 0 c)
    (weak := QRH.Record1252270103Source.globalFace B ℓ c) ⟨le_rfl, le_rfl, le_rfl, le_rfl, hℓ,
    show B - B ≤ (ℓ - 0)*0 by simp⟩ h

/-- **One stage point, one decrement.** -/
theorem stage_anchor (F : ParentFace) {R z k r : ℝ} (hS : StageHyp R z k r)
    (high : QRH.SilDensitySplit.CubeFree.Price) (hH : HighAt high R z k r) (hk0 : 0 ≤ k)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/1000)
    (href : Ordinary.Reference.ReferenceLaneFine (stageData F R z k r β high hk0 hβ0))
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    (hprev : ∀ δ' : ℝ, 0 < δ' → OrdinaryRectSource (anchorRect R z δ'))
    (hhigh : High.HighBranchMesh high k) :
    OrdinaryRectSource (anchorRect r (fY R z k r - stageDelta) β) := by
  have G := stageGates F hS high hH hk0 hβ0 hβ1
  have hd1 := del1_pos hβ0
  have hd1δ := del1_le_delta β
  have hdd : stageDelta = 1/25000000 := rfl
  have hsoft : QRH.Record1252270103Source.GlobalSource (R - del1 β) (β/4)
      ((1-R)/2 + z - del1 β) :=
    globalSource_soft (by linarith) (hprev (del1 β) hd1)
  have hleaf : PricedPackedSource (stageData F R z k r β high hk0 hβ0).price
      (stageData F R z k r β high hk0 hβ0).Hmin
      ((stageData F R z k r β high hk0 hβ0).Hmax + 1) 4 :=
    anchor_priced_source (R - del1 β) (β/4) ((1-R)/2 + z - del1 β) k (1/2) (3+1) 4 high
      (div_pos hβ0 (by norm_num)) hk0 (by linarith [hS.hk.1]) (by linarith [hS.hk.2]) hbeta
      ⟨by linarith [hS.hR.1], by linarith [hS.hR.2], by linarith [hS.hR.2, hS.hz]⟩
      (by norm_num) (by norm_num) hsoft hhigh
  exact Ordinary.anchor_ordinary_step_four _ G href hbeta hparent hleaf

/-- **The ordinary anchors of the chain.** For every stage `n < 256`, every `r ∈ [left n, R n]`
and every decrement `β > 0`: the ordinary rectangle `anchorRect r (Y_n(r) - δ) β`. -/
theorem chain_ordinary_anchor (F : ParentFace) (hL : ChainHighLedger) (n : ℕ) (hn : n < 256)
    (r : ℝ) (h1 : (left n : ℝ) ≤ r) (h2 : r ≤ R n)
    (href : ∀ β : ℝ, ∀ hβ0 : 0 < β, β ≤ 1/1000 →
      Ordinary.Reference.ReferenceLaneFine (stageData F (R n) (gain n) (cut n) r β
        (High.highPriceW (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000) (cut_nonneg n hn)
          (cut_le n hn))
        (cut_nonneg n hn) hβ0))
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    (hprev : ∀ δ' : ℝ, 0 < δ' → OrdinaryRectSource (anchorRect (R n) (gain n) δ'))
    (hhigh : High.HighBranchMesh (High.highPriceW (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000) (cut_nonneg n hn)
          (cut_le n hn))
      (cut n)) :
    ∀ β : ℝ, 0 < β →
      OrdinaryRectSource (anchorRect r (fY (R n : ℝ) (gain n) (cut n) r - stageDelta) β) := by
  have key : ∀ β : ℝ, ∀ hβ0 : 0 < β, β ≤ 1/1000 →
      OrdinaryRectSource (anchorRect r (fY (R n : ℝ) (gain n) (cut n) r - stageDelta) β) :=
    fun β hβ0 hβ1 => stage_anchor F (stageHyp_chain n hn r h1 h2) _ (highAt_chain hL n hn r h1 h2)
      (cut_nonneg n hn) hβ0 hβ1 (href β hβ0 hβ1) hbeta hparent hprev hhigh
  intro β hβ
  by_cases hle : β ≤ 1/1000
  · exact key β hβ hle
  · have hlt : (1/1000 : ℝ) < β := lt_of_not_ge hle
    exact (key (1/1000) (by norm_num) le_rfl).restrict
      (anchorRect_restricts (by linarith) (by linarith))

end
end Qrh.MarkedAnchor.Price
