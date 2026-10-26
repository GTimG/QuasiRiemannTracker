import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelBridge
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.TwoLevelPrice
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The LOW rate of the first step of the two-level ledger exceeds the rate at the slot price, and the reflection loss
that the joined row 5 absorbs in the gap. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open Cycle63 Cycle63.Optimization

/-- The reflection loss of the wrapper of the final daughter: the gap between the LOW rate of the ledger and the rate
`q/(6 slotPrice)` of the padding of the wrapper, times the least padding `εpad Mmin`. -/
def reflectionLoss [AffineLedger] (εpad Mmin : ℝ) : ℝ :=
  (AffineLedger.lowRate - AffineLedger.q / (6 * slotPrice)) * (εpad * Mmin)

/-- The reflection loss is positive when the rate of the padding is below the LOW rate. -/
theorem reflectionLoss_pos [AffineLedger] {εpad Mmin : ℝ}
    (hlt : AffineLedger.q / (6 * slotPrice) < AffineLedger.lowRate) (hep : 0 < εpad) (hmin : 0 < Mmin) :
    0 < reflectionLoss εpad Mmin :=
  mul_pos (sub_pos.mpr hlt) (mul_pos hep hmin)

/-- The LOW rate of the first step of the two-level ledger exceeds the rate at the slot price. -/
theorem rate_lt_lowRate [L : AffineLedger] [h : IsTwoLevelFirstStep L] :
    AffineLedger.q / (6 * slotPrice) < AffineLedger.lowRate := by
  unfold AffineLedger.lowRate
  rw [h.q_eq, h.price_eq]
  exact firstJunction_div_slotPrice_lt

/-- The absorption of the rate and of the reflection loss of the wrapper in the LOW rate of the first step of the
two-level ledger: the reflection loss is positive, the rate `q/(6 slotPrice)` is at most the LOW rate, and the
reflection loss is at most the gap of the rates times the least padding. -/
theorem two_level_absorption [L : AffineLedger] [IsTwoLevelFirstStep L] {εpad Mmin : ℝ} (hep : 0 < εpad)
    (hmin : 0 < Mmin) :
    0 < reflectionLoss εpad Mmin ∧ AffineLedger.q / (6 * slotPrice) ≤ AffineLedger.lowRate ∧
      reflectionLoss εpad Mmin ≤ (AffineLedger.lowRate - AffineLedger.q / (6 * slotPrice)) * (εpad * Mmin) :=
  ⟨reflectionLoss_pos rate_lt_lowRate hep hmin, rate_lt_lowRate.le, le_rfl⟩

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
