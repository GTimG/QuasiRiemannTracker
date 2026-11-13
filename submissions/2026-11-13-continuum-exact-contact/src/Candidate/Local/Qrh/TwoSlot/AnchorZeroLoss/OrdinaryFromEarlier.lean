/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The actual zero-stage-decrement ordinary anchor from preceding paired sources.
The original reference-lane proof is reused with the exact new step datum. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.OrdinaryStage
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Marked.TopSources
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.LeafBranch
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.StageBridge
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Reference.Lane

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss
noncomputable section
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
open Qrh.TwoSlot.AnchorExtension.ChainData

/-- All reference-lane gates for the zero-decrement ordinary datum. -/
theorem reference_lane_zero (F : ParentFace) {R z k r : ℝ}
    (hS : StageHyp R z k r) (high : QRH.SilDensitySplit.CubeFree.Price)
    (hk0 : 0≤k) {β : ℝ} (hβ : 0<β) (hβhi : β≤1/1000) :
    Ordinary.Reference.ReferenceLaneFine (stageData F R z k r β high hk0 hβ) := by
  apply Ordinary.Reference.reference_lane_fine (ρ:=1/100)
  have hc := stage_c_eq F high hk0 (r:=r) (z:=z) (R:=R) hβ
  have hlo := hS.S_lower
  have g2 := hS.g2
  have hr2 := hS.hr.2
  have hR2 := hS.hR.2
  have hlref : (stageData F R z k r β high hk0 hβ).lref=7/50 := rfl
  refine ⟨by norm_num,?_,?_,?_,?_,?_⟩
  · rw [hlref]; norm_num
  · rw [hc]; linarith
  · rw [hlref,hc]
    simp only [Ordinary.Reference.Lref,Ordinary.Reference.Bref]
    linarith
  · rw [hc]; simp only [Ordinary.Reference.cref]; linarith
  · rw [hlref,hc]; linarith

/-- Both the reference lane and the physical HIGH input are discharged here.
Only the actual parent, entry anchor, preceding anchors and scalar stage gates
remain as inputs. Every positive output decrement is retained. -/
theorem ordinary_anchor_of_earlier (F : ParentFace) {R z k r a0 a1 wlo T : ℝ}
    (hS : StageHyp R z k r)
    (hβ : (51/100:ℝ)≤OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    (hprev : AnchorAt R z)
    (hR : R<wlo) (hwlo : 0≤wlo) (hwlohi : wlo≤R+1/10000)
    (hwlocut : wlo≤High.cutHi) (hTlo : 3/4≤T) (hThi : T≤7/9)
    (ha : 0≤a1) (ha1 : a1≤2/5) (hl : a0-a1*T≤0)
    (hprior : ∀x : ℝ,R<x → x≤T → ∃gain : ℝ,0≤gain ∧ a0-a1*x≤gain ∧ AnchorAt x gain)
    (hledger : High.highPriceFW a0 a1 k wlo r (fs R z k r) (fH R r)≤fu R r) :
    ∀β : ℝ,0<β → OrdinaryRectSource (anchorRect r (fY R z k r) β) := by
  have hM := High.Marked.highMarkedCoreInputs_of_earlier hβ hres R T wlo a0 a1
    hR hwlo hTlo hThi ha ha1 hl hprior
  have hhigh := High.high_branch_mesh hβ
    (show 1/6≤k by linarith [hS.hk.1]) (show k≤3/4 by linarith [hS.hk.2])
    hwlocut ha (by linarith) hM
  have hH := High.highAt_stage hS hwlohi hledger
  exact ordinary_stage_zero_all F hS
    (High.highPriceW a0 a1 k wlo hS.k_pos.le (by linarith [hS.hk.2])) hH hS.k_pos.le
    (fun β hβ hβhi=>reference_lane_zero F hS _ _ hβ hβhi)
    hβ hparent (fun δ hδ=>(hprev δ hδ).2) hhigh

end
end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.ordinary_anchor_of_earlier
