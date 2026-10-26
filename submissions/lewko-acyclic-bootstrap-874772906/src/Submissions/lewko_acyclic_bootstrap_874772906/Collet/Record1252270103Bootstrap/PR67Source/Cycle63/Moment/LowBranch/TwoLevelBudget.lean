import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelCertificateValues
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelBridge
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The numeric budget of the returned HIGH parts of the two-level row 5: the losses of the second step and the slacks
of its certificates against the two-level HIGH margin less the LOW reserve. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open Cycle63 Cycle63.Optimization Cycle63.Certificate

/-- The losses of the returned HIGH parts of row 5 fit under the two-level HIGH margin less the LOW reserve: the
frequency loss `ωmax`, the shell slack `ε` and the padding `εpad` of at most `10⁻¹⁰`, the loss floor of the second
step of at most `10⁻⁹`, and the grid and amplifier slacks of `twoLevelCertificates_of_small` on a grid of at least
`10¹²` points. This is the numeric condition of `lowReturnedFacts_two_level`. -/
theorem twoLevelReturnedBudget [Led : Cycle63.AffineLedger] [IsTwoLevelFirstStep Led] {G : ℕ}
    {ωmax ε lossFloor εpad εwidth εold εlabels : ℝ} (hG : 10^12 ≤ G) (hω : 0 ≤ ωmax)
    (hω' : ωmax ≤ 1/10^10) (hε : ε ≤ 1/10^10) (hloss : lossFloor ≤ 1/10^9) (hpad : 0 ≤ εpad)
    (hpad' : εpad ≤ 1/10^10) (hew : 0 ≤ εwidth) (hold : 0 ≤ εold) (hel : 0 ≤ εlabels) :
    ωmax + ε + lossFloor + 3/4*(εpad + secondSlope/G) +
        23/7*(amplifierRatio slotPrice 1 secondJunction*(2*ωmax + εpad) +
          amplifierRatio slotPrice 1 secondJunction*(1 + 6*slotPrice)/G) <
      highTwoMargin - Cycle63.AffineLedger.lowReserve + εwidth/2 + εold + εlabels/2 +
        Cycle63.AffineLedger.lowRate*εpad := by
  rw [lowReserve_eq]
  have hmargin : 2/10^8 ≤ highTwoMargin :=
    le_min (by linarith [highTwoFirst_enclosure.1]) (by linarith [highTwoTop_enclosure.1])
  have hreserve := firstLowReserve_enclosure.2
  have hslope := secondSlope_bounds.2
  have hK := secondAmplifierRatio_bounds
  have hprice := slotPrice_mem
  have hrate : 0 ≤ Cycle63.AffineLedger.lowRate := by
    unfold Cycle63.AffineLedger.lowRate
    exact div_nonneg Led.q_pos.le (by linarith [Led.price_pos])
  have hG' : (10:ℝ)^12 ≤ G := by exact_mod_cast hG
  have hGpos : (0:ℝ) < G := lt_of_lt_of_le (by norm_num) hG'
  have hK0 : 0 ≤ amplifierRatio slotPrice 1 secondJunction := by linarith [hK.1]
  have hK3 : amplifierRatio slotPrice 1 secondJunction ≤ 3 := by linarith [hK.2]
  have hgrid : secondSlope/G ≤ 5/10^12 := by
    rw [div_le_iff₀ hGpos]
    linarith
  have hcost : amplifierRatio slotPrice 1 secondJunction*(1 + 6*slotPrice) ≤ 33/2 :=
    calc amplifierRatio slotPrice 1 secondJunction*(1 + 6*slotPrice)
        ≤ 3*(11/2) := mul_le_mul hK3 (by linarith [hprice.2]) (by linarith [hprice.1]) (by norm_num)
      _ = 33/2 := by norm_num
  have hampG : amplifierRatio slotPrice 1 secondJunction*(1 + 6*slotPrice)/G ≤ 2/10^11 := by
    rw [div_le_iff₀ hGpos]
    linarith
  have hampω : amplifierRatio slotPrice 1 secondJunction*(2*ωmax + εpad) ≤ 9/10^10 :=
    calc amplifierRatio slotPrice 1 secondJunction*(2*ωmax + εpad)
        ≤ 3*(3/10^10) := mul_le_mul hK3 (by linarith) (by linarith) (by norm_num)
      _ = 9/10^10 := by norm_num
  have hrp := mul_nonneg hrate hpad
  linarith
end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
