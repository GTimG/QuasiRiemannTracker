/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual inverse window mesh also pays P4's stored-band discrepancy.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafFees
set_option autoImplicit false
namespace QRH.Cycle092.RegularColoredForward
open QRH.SourceCertificate

/-- The same literal loss/10 table and early price used by genuine P6
fit the additional P4 window debit, retaining the actual witness m. -/
theorem terminal_shared_window_fee {loss price d dmax m : ℝ}
    (hloss : 0 ≤ loss) (hlossMax : loss ≤ (rho:ℝ)/64)
    (hp : 0 ≤ price) (hd : d ≤ dmax) (hm0 : 0 ≤ m) (hm : m ≤ 51/100)
    (hprice : price*dmax ≤ loss/4) :
    3*(loss/10)+price*d*m ≤ (rho:ℝ)/128 := by
  have hp1 : price*d ≤ loss/4 := (mul_le_mul_of_nonneg_left hd hp).trans hprice
  have hp2 : price*d*m ≤ (loss/4)*(51/100:ℝ) :=
    mul_le_mul hp1 hm hm0 (by positivity)
  have hrho : 0 ≤ (rho:ℝ) := by norm_num [rho]
  nlinarith

#print axioms terminal_shared_window_fee
end QRH.Cycle092.RegularColoredForward
