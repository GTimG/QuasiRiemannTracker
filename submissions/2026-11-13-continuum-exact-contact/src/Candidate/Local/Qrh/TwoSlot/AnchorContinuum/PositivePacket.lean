/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The physical packet exponent closes with an arbitrary positive fee. This
uses the literal numerator/kernel identity and retains every scalar loss;
it makes no new mean-value estimate. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.GenericScalar

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open QRH.Record1252270103Return
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Scalar
variable [Geometry.Parameters]
variable [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds]

/-- The reserve consumed by the count loss scales with the chosen fee. -/
theorem count_loss_reserve {d loss fee : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 1)
    (hfee : 0 ≤ fee) (hl : loss ≤ fee/4) : 3*d*loss/4 ≤ fee/2 := by
  have hm := mul_le_mul_of_nonneg_left hl hd
  have hn := mul_nonneg hfee (sub_nonneg.mpr hdhi)
  nlinarith only [hm,hn,hfee]

/-- The same actual packet identity used by the physical numerator permits
any positive fee, with reserve fee/2. The displayed row deficit is the scalar
input; no fixed numerical row fee or PhysicalSchedule instance is assumed. -/
theorem packet_certificate (bs : List Branch)
    {beta d C delta p e height fee : ℝ} (L : LossData)
    (hbeta : Geometry.theta < beta) (hfee : 0 < fee)
    (hrow : rowAt bs (2*beta-1) d C delta p-beta ≤
      -fee-(3/4)*(beta-Geometry.theta))
    (hbudget : 16*e+weightedSourceLoss d delta L+height ≤
      (beta-Geometry.theta)/4) :
    numeratorExponent bs (2*beta-1) d C delta p+
      kernelExponent ((1+delta)/2) e+weightedSourceLoss d delta L <
      beta+Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.signalShift-
        fee/2-(beta-Geometry.theta)/2-height := by
  have hi := numerator_kernel_exponent bs (2*beta-1) d C delta p e
  linarith only [hi,hrow,hbudget,hbeta,hfee]

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.count_loss_reserve
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.packet_certificate
