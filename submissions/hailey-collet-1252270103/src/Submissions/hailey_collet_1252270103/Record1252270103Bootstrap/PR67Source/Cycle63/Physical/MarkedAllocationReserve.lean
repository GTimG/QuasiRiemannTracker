import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.MarkedHighReserve
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-! The marked ledger in a cell `b` of the slot window and a bin `δ` of the marked range. A label
removes the width `R` at the common rate of the bin and keeps the live width `L` and the frequency
`q` of its live slots, at least the frequency of the cell less twice the removed width. The exact
marked gain of the live slots, the HIGH reserve and the removed width at the common rate then keep
the room `lowReserve` and the marked loss: the five channels of the ledger certify it on the supplied
width and the live frequency of the cell (`ExactGain.exact_gain_payment`). -/

namespace MarkedAllocationReserve
noncomputable section
open Cycle63.Arithmetic Cycle63.Optimization

/-- The frequency coordinate of a label in the cell `b` is at least the frequency of the cell less
twice the removed widths. -/
theorem raw_frequency_lower (cell M c d b a R Lc ω err q : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hb : 0 ≤ b) (hR : R ≤ c) (hLc : 0 ≤ Lc)
    (ha : a ≤ M*amp cell) (hω : ω ≤ M*frequencyLossCap) (herr : 0 ≤ err)
    (hq : q = M-R-max (c-d) 0+Lc-6*a-ω+err) :
    frequencyAt cell*M-2*(c+b) ≤ q := by
  have hm : max (c-d) 0 ≤ c := max_le (by linarith) hc
  unfold frequencyAt
  linarith

/-- The marked ledger: the HIGH reserve, the removed width at the common rate and the exact marked
gain of the live width at the live frequency keep the room `lowReserve` and the marked loss. -/
theorem marked_allocation_payment {b δ removed live q : ℝ}
    (hb : firstCellTop ≤ b ∧ b ≤ slotTop) (hδ : q0 ≤ δ ∧ δ ≤ markedBinTop)
    (hu : 0 ≤ removed) (hlive : 0 ≤ live) (hsupply : suppliedAt b ≤ removed+live)
    (hq : frequencyAt b-2*removed ≤ q) :
    lowReserve+markedLoss ≤
      Cycle63.Physical.highMainReserve b δ+commonRateAt δ*removed+markedGain δ live (coreFactor*q) := by
  obtain ⟨hφ, hu', hv, hslope⟩ := ledger_gain_facts hδ
  obtain ⟨hrate, hlinear, hmixed, hinverse, hcapped⟩ := ledger_channels hδ hb
  have hcore := coreFactor_bounds
  have hc : 0 ≤ capCoefficient δ := by unfold capCoefficient; positivity
  have hfreq : coreFactor*frequencyAt b ≤ 2*removed+coreFactor*q := by
    have h1 := mul_le_mul_of_nonneg_left hq (by linarith [hcore.1] : (0:ℝ) ≤ coreFactor)
    have h2 := mul_le_mul_of_nonneg_right (by linarith [hcore.2] : coreFactor ≤ 1) hu
    nlinarith
  rw [← highFee_eq]
  exact ExactGain.exact_gain_payment (by linarith) hu hφ.le hu'.le hv.le (supply_le_frequency hb)
    hslope.le hlive hsupply hfreq hrate hlinear hmixed hinverse hcapped

end
end MarkedAllocationReserve

end Record1252270103Bootstrap.PR67
