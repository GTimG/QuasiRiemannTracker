import Candidate.Cycle63.Physical.NonexceptionalLedger

namespace Cycle63.Physical
noncomputable section
open Cycle63.Arithmetic OAI.SevenEighths.LocalMoment

/-- Quantitative reserve growth above the lower high-zero cutoff. -/
theorem high_main_reserve_increase {b δ : ℝ}
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) (hd : q0≤δ ∧ δ≤3/4) :
    highMainReserve b q0+(δ-q0)*Cycle63.Optimization.reserveGrowth≤highMainReserve b δ := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have hδ : 0<5-2*δ := by linarith [hd.2]
  have hq : 0<5-2*q0 := by linarith [q0_bounds.2]
  have hden : 0<3*(5-2*δ)*(5-2*q0) := by positivity
  have hn : 0≤50*(1-6*amp b) := by
    have ha := (amp_bounds hb).2
    linarith [Cycle63.Optimization.amplifierCap_bounds.2]
  have hprod : 3*(5-2*δ)*(5-2*q0)≤3*(5-2*q0)^2 := by nlinarith [hd.1]
  have hfrac := div_le_div_of_nonneg_left hn hden hprod
  have hbase := high_derivative_reserve hb
  have hder : Cycle63.Optimization.reserveGrowth≤50*(1-6*amp b)/(3*(5-2*δ)*(5-2*q0))-totalA b := by
    linarith
  have hid : highMainReserve b δ-highMainReserve b q0=
      (δ-q0)*(50*(1-6*amp b)/(3*(5-2*δ)*(5-2*q0))-totalA b) := by
    unfold highMainReserve unmarkedDensity
    field_simp [hδ.ne',hq.ne',show 5-δ*2≠0 by linarith [hd.2],show 5-q0*2≠0 by linarith]
    ring
  have hh := mul_le_mul_of_nonneg_left hder (sub_nonneg.mpr hd.1)
  rw [←hid] at hh
  linarith

/-- In the cell `b` the net saving of the supplied width at the price pays for the enlarged affine
intercept and leaves the room `lowReserve`. -/
theorem marked_high_reserve {b δ : ℝ}
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) (hd : q0≤δ ∧ δ≤3/4) :
    lowReserve≤highMainReserve b δ+
      (markedPrice*Cycle63.Optimization.suppliedAt b-Cycle63.Optimization.markedLoss) := by
  have hh := high_main_reserve_bound hb hd
  linarith

/-- The net marked saving of the cell `b` and the bin `δ` pays for the enlarged affine intercept and
leaves the room `lowReserve`: above the bin split the HIGH reserve grows faster than the live end of
the ledger falls. -/
theorem marked_high_reserve_at {b δ : ℝ}
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) (hd : q0≤δ ∧ δ≤3/4) :
    lowReserve≤highMainReserve b δ+(markedGrossAt b δ-Cycle63.Optimization.markedLoss) := by
  have hinc := high_main_reserve_increase hb hd
  have hr := high_main_reserve_bound hb (show q0≤q0 ∧ q0≤3/4 from ⟨le_rfl,by linarith [q0_bounds.2]⟩)
  have hdrop := markedGross_drop (b := b) hd
  have hsplit := markedGross_split (b := b) (by unfold Cycle63.Optimization.slotTop; exact hb.2)
  linarith

/-- At the bin top the growth of the HIGH reserve above the bin split pays the net marked saving of
every cell. -/
theorem window_top_growth {b : ℝ} (hb : b≤Cycle63.Optimization.slotTop) :
    markedPrice*Cycle63.Optimization.suppliedAt b-Cycle63.Optimization.markedLoss≤
      (Cycle63.Optimization.markedBinTop-q0)*Cycle63.Optimization.reserveGrowth := by
  have hp : markedPrice = Cycle63.Optimization.priceEndRate Cycle63.Optimization.markedSplit := by
    rw [markedPrice_eq]; rfl
  have htop : (Cycle63.Optimization.markedBinTop-q0)*Cycle63.Optimization.reserveGrowth =
      Cycle63.Optimization.priceEndRate Cycle63.Optimization.markedSplit*
        Cycle63.Optimization.suppliedAt Cycle63.Optimization.slotTop-Cycle63.Optimization.markedLoss :=
    Cycle63.Optimization.bin_top_growth.symm
  have hs : Cycle63.Optimization.suppliedAt b ≤ Cycle63.Optimization.suppliedAt Cycle63.Optimization.slotTop := by
    unfold Cycle63.Optimization.suppliedAt; linarith
  have hpos := markedPrice_pos
  have hmul := mul_le_mul_of_nonneg_left hs hpos.le
  rw [hp] at hmul
  rw [hp]
  linarith

/-- The unmarked argument already suffices above the bin top. -/
theorem unmarked_upper_high_reserve {b δ : ℝ}
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) (hd : Cycle63.Optimization.markedBinTop≤δ ∧ δ≤3/4) :
    lowReserve≤highMainReserve b δ := by
  have hq := q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hgr := Cycle63.Optimization.reserveGrowth_bounds
  have hδ : q0≤δ ∧ δ≤3/4 := ⟨by linarith [hd.1],hd.2⟩
  have hh := high_main_reserve_increase hb hδ
  have hr := high_main_reserve_bound hb (show q0≤q0 ∧ q0≤3/4 from ⟨le_rfl,by linarith⟩)
  have hg := window_top_growth hb.2
  have hmono := mul_le_mul_of_nonneg_right (sub_le_sub_right hd.1 q0) (by linarith [hgr.1] :
    (0:ℝ)≤Cycle63.Optimization.reserveGrowth)
  linarith

end
end Cycle63.Physical
#print axioms Cycle63.Physical.marked_high_reserve
#print axioms Cycle63.Physical.marked_high_reserve_at
#print axioms Cycle63.Physical.unmarked_upper_high_reserve
