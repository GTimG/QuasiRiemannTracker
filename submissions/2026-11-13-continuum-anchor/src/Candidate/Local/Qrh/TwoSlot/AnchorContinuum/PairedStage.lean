/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ToleranceConsumer
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.PairedStage

/-! The actual paired step at a variable coupled tolerance. All remaining
stage inequalities are explicit scalar hypotheses; the inverse and ordinary
physical HIGH inputs are constructed from preceding paired anchors. -/

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum
noncomputable section
open Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
open Qrh.TwoSlot.AnchorExtension.ChainData
open Qrh.TwoSlot.AnchorZeroLoss

theorem paired_anchor_of_earlier [shift : High.WitnessShift]
    (F : ParentFace) {R z k r a0 a1 wlo T : ℝ}
    (hS : StageHyp R z k r)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    (hprev : AnchorAt R z)
    (hR : R < wlo) (hwlo : 0 ≤ wlo) (hwlohi : wlo ≤ R+1/10000)
    (hwlocut : wlo ≤ High.cutHi) (hTlo : 3/4 ≤ T) (hThi : T ≤ 7/9)
    (ha : 0 ≤ a1) (ha1 : a1 ≤ 2/5) (hl : a0-a1*T ≤ 0)
    (hprior : ∀ x : ℝ, R < x → x ≤ T → ∃ gain : ℝ,
      0 ≤ gain ∧ a0-a1*x ≤ gain ∧ AnchorAt x gain)
    (htiny : High.tinyEx r (fs R z k r) (fH R r) ≤ fu R r-3/100)
    (hclasses : ∀ p ∈ High.classes k, ∃ w ∈ High.cutoffs, wlo ≤ w ∧
      w+Tolerances.sig High.WitnessShift.value a0 a1 w ≤ 6 ∧
      Tolerances.detEx High.WitnessShift.value a0 a1 p.1 p.2 w
        r (fs R z k r) (fH R r) ≤ fu R r) :
    AnchorAt r (fY R z k r) := by
  let a0' := Tolerances.intercept High.WitnessShift.value a0
  have hclasses' : ∀ p ∈ High.classes k, ∃ w ∈ High.cutoffs, wlo ≤ w ∧
      w+High.sig a0' a1 w ≤ 6 ∧
      High.detEx a0' a1 p.1 p.2 w r (fs R z k r) (fH R r) ≤ fu R r := by
    intro p hp
    obtain ⟨w,hw,hlo,hsig,hd⟩ := hclasses p hp
    refine ⟨w,hw,hlo,?_,?_⟩
    · simpa only [a0', Tolerances.sig_recenter] using hsig
    · simpa only [a0', Tolerances.parametric_price_eq] using hd
  have hledger : High.highPriceFW a0' a1 k wlo r (fs R z k r) (fH R r) ≤ fu R r := by
    have h := High.highPriceFW_le_of (a0:=a0') (a1:=a1) (wlo:=wlo)
      hS.k_pos.le (show k ≤ 3/4 by linarith [hS.hk.2])
      (show High.tinyEx r (fs R z k r) (fH R r) ≤ fu R r by linarith)
      (fun p hp => by
        obtain ⟨w,hw,hlo,_,hd⟩ := hclasses' p hp
        exact ⟨w,hw,hlo,hd⟩)
    simpa only [max_eq_right hS.u_nonneg] using h
  have hMraw := Tolerances.markedCore_of_earlier hβ hres
    High.WitnessShift.pos High.WitnessShift.le_fixed R T wlo a0 a1
    hR hwlo hTlo hThi ha ha1 hl hprior
  have hM := Tolerances.marked_core_recenter hMraw
  have hhigh := High.high_branch_mesh hβ
    (show 1/6 ≤ k by linarith [hS.hk.1]) (show k ≤ 3/4 by linarith [hS.hk.2])
    hwlocut ha (by linarith) (High.Inverse.highMarkedCoreInputsH_of_R1 hM)
  have hH := High.highAt_stage hS hwlohi hledger
  have hord := ordinary_stage_zero_all F hS
    (High.highPriceW a0' a1 k wlo hS.k_pos.le (by linarith [hS.hk.2])) hH hS.k_pos.le
    (fun β hβ hβhi => reference_lane_zero F hS _ _ hβ hβhi)
    hβ hparent (fun δ hδ => (hprev δ hδ).2) hhigh
  have hpriced := High.Inverse.inverseHighLeaf a0' a1 k wlo hβ
    (by linarith [hS.hk.1]) (by linarith [hS.hk.2]) ha (by linarith) hwlocut hM
  have hinv := inverse_anchor_of_priced hS hprev hpriced
    (zero_child_price hS htiny hclasses')
  exact fun δ hδ => ⟨hinv δ hδ,hord δ hδ⟩

end
end Qrh.TwoSlot.AnchorContinuum
