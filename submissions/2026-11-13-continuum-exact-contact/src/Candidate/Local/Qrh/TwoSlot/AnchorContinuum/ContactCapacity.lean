/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Physical slot-capacity bounds for the exact critical tangent. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ContactSource

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section

instance exact_capacity : Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.CapacityBounds exactLine where
  bounds := by
    intro w hlo hhi
    simp only [Qrh.MarkedAnchor.Interface.anchorLeft,Qrh.MarkedAnchor.Interface.anchorTop] at hlo hhi
    have hc := tangent_coefficient_bounds
    have hm0 := mul_le_mul_of_nonneg_right hc.2.2.1.le (show 0 ≤ w by linarith)
    have hm1 := mul_le_mul_of_nonneg_right hc.2.2.2.le (show 0 ≤ w by linarith)
    change (1/10000000:ℝ) < (1-w)/2+tangentIntercept-(-tangentSlope)*w ∧
      (1-w)/2+tangentIntercept-(-tangentSlope)*w ≤ 7/37
    constructor <;> nlinarith [hc.1,hc.2.1]

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.exact_capacity
