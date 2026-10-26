import Candidate.Target836.Source836.GlobalNamed
import Candidate.Cycle63.Physical.TerminalLedger
namespace OAI.SevenEighths.Target836SourceAssembly
noncomputable section
open GlobalNamed
 theorem second_zero_excess_bound {b M A a c d Bc : ℝ}
    (hb : 3401/100000≤b ∧ b≤1/25) (hM : 0≤M)
    (hA : A≤M*totalA b) (ha : a≤M*amp b)
    (hc : 0≤c) (hd : 0≤d) (hBc : 0≤Bc) :
    A-M-min c d-Bc+5*a≤-M*(227876729/3446640000) := by
  have hreserve := mul_le_mul_of_nonneg_left (GlobalNamed.second_zero_reserve hb) hM
  have hmin : 0≤ min c d := le_min hc hd
  nlinarith
end
end OAI.SevenEighths.Target836SourceAssembly
#print axioms OAI.SevenEighths.Target836SourceAssembly.second_zero_excess_bound
