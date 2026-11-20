/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
O.2 HIGH and inverse-child ledgers, reusing the same actual original source. -/
import Candidate.C092.transport.TangentExtensionInverse
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.StageBridge
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorZeroLoss.PairedStage
set_option autoImplicit false
namespace QRH.Cycle092.TangentExtension
noncomputable section
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price Qrh.TwoSlot.AnchorZeroLoss
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
open Qrh.TwoSlot.AnchorExtension.ChainData
/-- The parent class ledger pays every point of the inverse child rectangle. -/
theorem zero_child_price [shift : Qrh.TwoSlot.AnchorZeroLoss.High.WitnessShift] {R z k r a0 a1 wlo : ℝ} (hS : StageHyp R z k r)
    (htiny : Qrh.TwoSlot.AnchorZeroLoss.High.tinyEx r (fs R z k r) (fH R r)≤fu R r-3/100)
    (hclasses : ∀p∈Qrh.TwoSlot.AnchorZeroLoss.High.classes k,∃w∈Qrh.TwoSlot.AnchorZeroLoss.High.cutoffs,wlo≤w ∧
      w+Qrh.TwoSlot.AnchorZeroLoss.High.sig a0 a1 w≤6 ∧ Qrh.TwoSlot.AnchorZeroLoss.High.detEx a0 a1 p.1 p.2 w r (fs R z k r) (fH R r)≤fu R r)
    (β : ℝ) (hb : 0<β) (hbhi : β≤1/1000) (P S : ℝ)
    (hadm : (zeroChild R z k r β).Admissible P S 1) :
    Qrh.TwoSlot.AnchorZeroLoss.High.highPriceFW a0 a1 k wlo P S 1≤zeroExcess R r β := by
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
  change Qrh.TwoSlot.AnchorZeroLoss.High.highPriceFW a0 a1 k wlo P S 1≤fu R r/(1-6*fu R r-β/8)
  rw [heq]
  exact Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.child_highPriceFW_le (by linarith [hS.hk.1])
    (by linarith [hS.hk.2]) hu0 (by linarith) (by linarith) hpos
    (by linarith) hPpaid hSpaid htiny hclasses

/-- The new price satisfies exactly the generic ledger contract consumed by
our compiled zero-stage-decrement ordinary step. The physical HIGH leaf
itself remains a separate source obligation. -/
theorem highAt_stage {a0 a1 R z k r wlo : ℝ}
    (hS : StageHyp R z k r)
    (hwlo : wlo ≤ R+1/10000)
    (hled : Qrh.TwoSlot.AnchorZeroLoss.High.highPriceFW a0 a1 k wlo r (fs R z k r) (fH R r) ≤ fu R r) :
    Qrh.MarkedAnchor.Price.HighAt
      (Qrh.TwoSlot.AnchorZeroLoss.High.highPriceW a0 a1 k wlo hS.k_pos.le (by linarith [hS.hk.2])) R z k r where
  antiM w P s M M' hM := Qrh.TwoSlot.AnchorZeroLoss.High.highPriceFW_antitoneM (by linarith [hS.hk.1])
    (by linarith [hS.hk.2]) P s hM
  ledger w := hled
  empty w := Qrh.TwoSlot.AnchorZeroLoss.High.empty_at_stage hS.hk.1 (by linarith [hS.hk.2]) hS.hR.1 hS.hR.2
    (by have h := hS.H_ge; unfold fH at h; linarith) hwlo

end
end QRH.Cycle092.TangentExtension
#print axioms QRH.Cycle092.TangentExtension.highAt_stage
