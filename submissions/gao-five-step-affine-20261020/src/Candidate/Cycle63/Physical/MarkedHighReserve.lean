import Candidate.Cycle63.Physical.NonexceptionalLedger

/-! The HIGH reserve `highMainReserve b δ` is the reserve of the channel ledger's plane at the bin
split (`highMainReserve_eq`), and the room `lowReserve` plus the marked loss is its fee
(`highFee_eq`), so the certificates of the channel ledger pay it. -/

namespace Cycle63.Physical
noncomputable section
open Cycle63.Arithmetic Cycle63.Optimization

/-- In a bin of the marked range the HIGH reserve and the supplied width removed at the common rate
keep the room `lowReserve` and the marked loss. -/
theorem marked_high_reserve {b δ : ℝ} (hb : firstCellTop≤b ∧ b≤ slotTop) (hd : q0≤δ ∧ δ≤ markedBinTop) :
    lowReserve+markedLoss≤highMainReserve b δ+commonRateAt δ*suppliedAt b := by
  rw [← highFee_eq]
  exact (ledger_channels hd hb).1

/-- From the bin top on the HIGH reserve alone keeps the room `lowReserve` and the marked loss. -/
theorem unmarked_upper_high_reserve {b δ : ℝ} (hb : firstCellTop≤b ∧ b≤ slotTop)
    (hd : markedBinTop≤δ ∧ δ≤3/4) : lowReserve+markedLoss≤highMainReserve b δ := by
  rw [← highFee_eq]
  exact ledger_unmarked hd hb

end
end Cycle63.Physical
