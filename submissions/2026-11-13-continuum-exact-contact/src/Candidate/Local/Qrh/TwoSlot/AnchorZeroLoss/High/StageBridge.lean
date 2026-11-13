/- Copyright (c) 2026 Sil. Apache-2.0.
Modified by Joseph Bebel (2026-11-12): bridge the 1e-13/1e-12 price into
the existing physical ordinary step. The old checkpoint is unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.PriceFloor
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.OrdinaryStage

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss.High
noncomputable section
variable [shift : WitnessShift]
open Qrh.TwoSlot.AnchorExtension.ChainData

theorem empty_at_stage {a0 a1 k wlo R r : ℝ} (hk : 45457/125000 ≤ k) (hk1 : k ≤ 3/4)
    (hR0 : 7/10 ≤ R) (hR1 : R ≤ 7/9) (hH : 1/2 ≤ r/R) (hwlo : wlo ≤ R + 1/10000) :
    highPriceFW a0 a1 k wlo r 0 (r/R) ≤ 0 := by
  have hshift0 := WitnessShift.pos
  have hshift1 := WitnessShift.le_fixed
  have hRpos : 0 < R := by linarith
  set H := r/R with hHdef
  have hr' : r = H*R := by rw [hHdef, div_mul_cancel₀ r hRpos.ne']
  have h := highPriceFW_le_of (a0 := a0) (a1 := a1) (k := k) (wlo := wlo) (P := r) (s := 0) (M := H)
    (c := 0) (by linarith) hk1 ?tiny ?det
  · simpa using h
  case tiny =>
    unfold tinyEx
    rw [hr']
    nlinarith
  case det =>
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    refine ⟨R + 1/10000, ⟨by unfold cutLo; linarith, by unfold cutHi; linarith⟩, hwlo, ?_⟩
    have hσ : 0 ≤ H * sig a0 a1 (R + 1/10000) :=
      mul_nonneg (by linarith) (sig_nonneg _ _ _)
    unfold detEx shortCnt longCnt
    rw [min_eq_left hσ]
    have hRA : R - (3*(R + 1/10000)/2 + WitnessShift.value) < 0 := by linarith
    have hν : p.1*(R - (3*(R + 1/10000)/2 + WitnessShift.value)) ≤
        (45457/125000)*(R - (3*(R + 1/10000)/2 + WitnessShift.value)) :=
      mul_le_mul_of_nonpos_right (by linarith) hRA.le
    have hbr : p.1*(R - (3*(R + 1/10000)/2 + WitnessShift.value)) + 1/6 +
        5*(3*(R + 1/10000)/2 + WitnessShift.value)/6 - 1 ≤ 0 := by linarith
    have hshort : H - p.1*H*(R + 1/10000) - p.2*0 ≤ H - p.1*r := by
      rw [hr']
      have : 0 ≤ p.1*H := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hlong : H/6 + (5/6 - p.1)*H*(3*(R + 1/10000)/2 + WitnessShift.value) ≤ H - p.1*r := by
      have key : H/6 + (5/6 - p.1)*H*(3*(R + 1/10000)/2 + WitnessShift.value) - (H - p.1*r) =
          H*(p.1*(R - (3*(R + 1/10000)/2 + WitnessShift.value)) + 1/6 +
            5*(3*(R + 1/10000)/2 + WitnessShift.value)/6 - 1) := by
        rw [hr']; ring
      have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ H by linarith) hbr
      linarith
    have := max_le hshort hlong
    linarith


/-- The new price satisfies exactly the generic ledger contract consumed by
our compiled zero-stage-decrement ordinary step. The physical HIGH leaf
itself remains a separate source obligation. -/
theorem highAt_stage {a0 a1 R z k r wlo : ℝ}
    (hS : Qrh.MarkedAnchor.Price.StageHyp R z k r)
    (hwlo : wlo ≤ R+1/10000)
    (hled : highPriceFW a0 a1 k wlo r (fs R z k r) (fH R r) ≤ fu R r) :
    Qrh.MarkedAnchor.Price.HighAt
      (highPriceW a0 a1 k wlo hS.k_pos.le (by linarith [hS.hk.2])) R z k r where
  antiM w P s M M' hM := highPriceFW_antitoneM (by linarith [hS.hk.1])
    (by linarith [hS.hk.2]) P s hM
  ledger w := hled
  empty w := empty_at_stage hS.hk.1 (by linarith [hS.hk.2]) hS.hR.1 hS.hR.2
    (by have h := hS.H_ge; unfold fH at h; linarith) hwlo

end
end Qrh.TwoSlot.AnchorZeroLoss.High
#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.highAt_stage
