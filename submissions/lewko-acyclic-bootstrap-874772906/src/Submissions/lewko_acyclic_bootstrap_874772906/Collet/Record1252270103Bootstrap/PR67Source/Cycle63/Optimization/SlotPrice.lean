import Mathlib.Tactic
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The slot price of the moment bounds, as a function of the bound on the real parts of the zeros
that it uses. Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.Optimization

noncomputable section

/-- The bound `β ≤ betaBound` on the supremum `β` of the real parts of the zeros of the Hecke family
that the slot prices use: the bound `10499/12000` of Akash Levy's weighted-numerator proof
(submission `akashlevy-20261009-weighted-numerator`, `WeightedQRH.beta_le_theta`; used in
`Cycle63.Assembly.beta_le_betaBound`). -/
def betaBound : ℝ := 10499/12000

/-- The slot price of the LOW half, of the error branch and of the slot amplitudes: their moment
bounds hold at every price `κ ≥ max (7/10) (2 β - 1)`, so at `2 betaBound - 1`. A deleted slot of
width `w` costs `6 κ w` of the capacity, and its amplitude is at most `Z^(κ w)`. -/
def slotPrice : ℝ := 2*betaBound - 1

/-- The slot price lies above the split range `[1/2, 37/50]` and at most at the baseline's price `3/4`. -/
theorem slotPrice_mem : 37/50 < slotPrice ∧ slotPrice ≤ 3/4 := by
  constructor <;> norm_num [slotPrice, betaBound]

theorem slotPrice_pos : 0 < slotPrice := by linarith [slotPrice_mem.1]

end

end Cycle63.Optimization

end Record1252270103Bootstrap.PR67
