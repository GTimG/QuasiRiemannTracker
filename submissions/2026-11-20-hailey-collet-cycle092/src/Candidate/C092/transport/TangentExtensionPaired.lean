/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine O.2 paired step at the extended anchor, from earlier sources. -/
import Candidate.C092.transport.TangentExtensionLedgers
import Candidate.C092.transport.TangentExtensionReference
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Marked.TopSources
set_option autoImplicit false
noncomputable section
namespace QRH.Cycle092.TangentExtension
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price Qrh.TwoSlot.AnchorZeroLoss
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
open Qrh.TwoSlot.AnchorExtension.ChainData

theorem paired_anchor_of_earlier (F : ParentFace) {R z k r a0 a1 wlo T : ℝ}
    (hS : StageHyp R z k r)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    (hprev : AnchorAt R z)
    (hR : R < wlo) (hwlo : 0 ≤ wlo) (hwlohi : wlo ≤ R+1/10000)
    (hwlocut : wlo ≤ Qrh.TwoSlot.AnchorZeroLoss.High.cutHi) (hTlo : 3/4 ≤ T) (hThi : T ≤ 7/9)
    (ha : 0 ≤ a1) (ha1 : a1 ≤ 2/5) (hl : a0-a1*T ≤ 0)
    (hprior : ∀ x : ℝ,R < x → x ≤ T → ∃ gain : ℝ,
      0 ≤ gain ∧ a0-a1*x ≤ gain ∧ AnchorAt x gain)
    (htiny : Qrh.TwoSlot.AnchorZeroLoss.High.tinyEx r (fs R z k r) (fH R r) ≤ fu R r-3/100)
    (hclasses : ∀ p∈Qrh.TwoSlot.AnchorZeroLoss.High.classes k,∃ w∈Qrh.TwoSlot.AnchorZeroLoss.High.cutoffs,wlo ≤ w ∧
      w+Qrh.TwoSlot.AnchorZeroLoss.High.sig a0 a1 w ≤ 6 ∧
      Qrh.TwoSlot.AnchorZeroLoss.High.detEx a0 a1 p.1 p.2 w r (fs R z k r) (fH R r) ≤ fu R r) :
    AnchorAt r (fY R z k r) := by
  have hledger : Qrh.TwoSlot.AnchorZeroLoss.High.highPriceFW a0 a1 k wlo r (fs R z k r) (fH R r) ≤ fu R r := by
    have h := Qrh.TwoSlot.AnchorZeroLoss.High.highPriceFW_le_of (a0:=a0) (a1:=a1) (wlo:=wlo)
      hS.k_pos.le (show k ≤ 3/4 by linarith [hS.hk.2])
      (show Qrh.TwoSlot.AnchorZeroLoss.High.tinyEx r (fs R z k r) (fH R r) ≤ fu R r by linarith)
      (fun p hp=>by
        obtain ⟨w,hw,hlo,_,hd⟩ := hclasses p hp
        exact ⟨w,hw,hlo,hd⟩)
    simpa only [max_eq_right hS.u_nonneg] using h
  have hM := Qrh.TwoSlot.AnchorZeroLoss.High.Marked.markedCore_of_earlier hβ hres R T wlo a0 a1
    hR hwlo hTlo hThi ha ha1 hl hprior
  have hhigh := Qrh.TwoSlot.AnchorZeroLoss.High.high_branch_mesh hβ
    (show 1/6 ≤ k by linarith [hS.hk.1]) (show k ≤ 3/4 by linarith [hS.hk.2])
    hwlocut ha (by linarith) (Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.highMarkedCoreInputsH_of_R1 hM)
  have hH := highAt_stage hS hwlohi hledger
  have hord := ordinary_stage_zero_all F hS
    (Qrh.TwoSlot.AnchorZeroLoss.High.highPriceW a0 a1 k wlo hS.k_pos.le (by linarith [hS.hk.2])) hH hS.k_pos.le
    (fun β hβ hβhi=>reference_lane_zero F hS _ _ hβ hβhi)
    hβ hparent (fun δ hδ=>(hprev δ hδ).2) hhigh
  have hpriced := Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.inverseHighLeaf a0 a1 k wlo hβ
    (by linarith [hS.hk.1]) (by linarith [hS.hk.2]) ha (by linarith) hwlocut hM
  have hinv := inverse_anchor_of_priced hS hprev hpriced
    (zero_child_price hS htiny hclasses)
  exact fun δ hδ=>⟨hinv δ hδ,hord δ hδ⟩

end QRH.Cycle092.TangentExtension
#print axioms QRH.Cycle092.TangentExtension.paired_anchor_of_earlier
