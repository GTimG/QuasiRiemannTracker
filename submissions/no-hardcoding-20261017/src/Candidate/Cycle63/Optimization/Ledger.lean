/- The valuation price of removed slot width and the range of bin splits.
Released under Apache 2.0. -/
import Candidate.Cycle63.Optimization.MarkedSplit

set_option autoImplicit false

namespace Cycle63.Optimization

noncomputable section

/-- The common-prime rate of the valuation estimate at the bin split `q`
(`first_common_valuation_uniform`): the price per unit of removed slot width. -/
def ledgerPrice (q : ℝ) : ℝ := q - max (4*density q - 1) ((2 + 22*density q)/21)

def splitRange : Set ℝ := Set.Icc (1/2) (37/50)

theorem mem_splitRange {q : ℝ} (hq : q ∈ splitRange) : 0 < q ∧ q < 3/4 :=
  ⟨by have := hq.1; linarith, by have := hq.2; linarith⟩

end

end Cycle63.Optimization
