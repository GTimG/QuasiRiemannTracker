/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Generic paired zero-stage-decrement anchor step. Physical source estimates
are supplied by the proved earlier-anchor adapters; the remaining gates are
explicit scalar comparisons. No numerical stage table occurs in its statement or proof. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.OrdinaryFromEarlier
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.InverseFromEarlier
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.Ledger

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss
noncomputable section
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
open Qrh.TwoSlot.AnchorExtension.ChainData

/-- The parent class ledger pays every point of the inverse child rectangle. -/
theorem zero_child_price [shift : High.WitnessShift] {R z k r a0 a1 wlo : ℝ} (hS : StageHyp R z k r)
    (htiny : High.tinyEx r (fs R z k r) (fH R r)≤fu R r-3/100)
    (hclasses : ∀p∈High.classes k,∃w∈High.cutoffs,wlo≤w ∧
      w+High.sig a0 a1 w≤6 ∧ High.detEx a0 a1 p.1 p.2 w r (fs R z k r) (fH R r)≤fu R r)
    (β : ℝ) (hb : 0<β) (hbhi : β≤1/1000) (P S : ℝ)
    (hadm : (zeroChild R z k r β).Admissible P S 1) :
    High.highPriceFW a0 a1 k wlo P S 1≤zeroExcess R r β := by
  have hu0 := hS.u_nonneg
  have hu := hS.hu
  have hH := hS.H_ge
  have hH1 := hS.H_le_one
  have hpos : 0<fH R r-β/8 := by linarith
  have heq : 1-6*fu R r-β/8=fH R r-β/8 := by rw [hS.H_eq]
  rcases hadm with ⟨hP0,hP,hS0,hSS⟩
  change P≤((r-β+2*(β/8))/(1-6*fu R r-β/8))*1 at hP
  change S≤(((1-r)/2+fY R z k r-β-fu R r+3*(β/8))/(1-6*fu R r-β/8))*1 at hSS
  rw [mul_one,heq] at hP hSS
  have hp := (le_div_iff₀ hpos).mp hP
  have hs := (le_div_iff₀ hpos).mp hSS
  have hPpaid : (fH R r-β/8)*P≤r-β+2*(β/8) := by nlinarith only [hp]
  have hSpaid : (fH R r-β/8)*S≤fs R z k r := by
    dsimp only [fs,fS]
    nlinarith only [hs,hu0,hb]
  change High.highPriceFW a0 a1 k wlo P S 1≤fu R r/(1-6*fu R r-β/8)
  rw [heq]
  exact High.Inverse.child_highPriceFW_le (by linarith [hS.hk.1])
    (by linarith [hS.hk.2]) hu0 (by linarith) (by linarith) hpos
    (by linarith) hPpaid hSpaid htiny hclasses

/-- One genuine paired anchor, with no fixed stage decrement and all positive
rectangle decrements, from the entry anchor and preceding paired anchors. -/
theorem paired_anchor_of_earlier (F : ParentFace) {R z k r a0 a1 wlo T : ℝ}
    (hS : StageHyp R z k r)
    (hβ : (51/100:ℝ)≤OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    (hprev : AnchorAt R z)
    (hR : R<wlo) (hwlo : 0≤wlo) (hwlohi : wlo≤R+1/10000)
    (hwlocut : wlo≤High.cutHi) (hTlo : 3/4≤T) (hThi : T≤7/9)
    (ha : 0≤a1) (ha1 : a1≤2/5) (hl : a0-a1*T≤0)
    (hprior : ∀x : ℝ,R<x → x≤T → ∃gain : ℝ,0≤gain ∧ a0-a1*x≤gain ∧ AnchorAt x gain)
    (htiny : High.tinyEx r (fs R z k r) (fH R r)≤fu R r-3/100)
    (hclasses : ∀p∈High.classes k,∃w∈High.cutoffs,wlo≤w ∧
      w+High.sig a0 a1 w≤6 ∧ High.detEx a0 a1 p.1 p.2 w r (fs R z k r) (fH R r)≤fu R r) :
    AnchorAt r (fY R z k r) := by
  have hledger : High.highPriceFW a0 a1 k wlo r (fs R z k r) (fH R r)≤fu R r := by
    have h := High.highPriceFW_le_of (a0:=a0) (a1:=a1) (wlo:=wlo)
      hS.k_pos.le (show k≤3/4 by linarith [hS.hk.2])
      (show High.tinyEx r (fs R z k r) (fH R r)≤fu R r by linarith)
      (fun p hp=>by
        obtain ⟨w,hw,hlo,hsig,hd⟩ := hclasses p hp
        exact ⟨w,hw,hlo,hd⟩)
    simpa only [max_eq_right hS.u_nonneg] using h
  have hord := ordinary_anchor_of_earlier F hS hβ hres hparent hprev
    hR hwlo hwlohi hwlocut hTlo hThi ha ha1 hl hprior hledger
  have hinv := inverse_anchor_of_earlier hS hβ hres hprev
    hR hwlo hwlocut hTlo hThi ha ha1 hl hprior (zero_child_price hS htiny hclasses)
  exact fun δ hδ=>⟨hinv δ hδ,hord δ hδ⟩

end
end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.paired_anchor_of_earlier
