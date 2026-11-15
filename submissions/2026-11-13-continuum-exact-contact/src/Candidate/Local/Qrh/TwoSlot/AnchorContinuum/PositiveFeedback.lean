/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Actual-supremum feedback and physical packet loss ledger at an arbitrary
positive row fee. Adapted from PR137 GenericFeedback and SourceLedger
(Sil, Hailey Collet and predecessor authors, Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositivePacket
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.SourceLedger

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open Set
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Scalar
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
variable [Geometry.Parameters]
variable [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds]

/-- The admitted envelope's parameter increase is paid before subtracting the
actual supremum. No fixed numerical fee or physical schedule is used. -/
theorem row_supremum_deficit (bs : List Branch) {beta d cap delta p fee : ℝ}
    (hgap : Geometry.theta < beta) (hd : d ∈ Icc (0:ℝ) 1)
    (hdelta : delta ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2))
    (hbase : rowAt bs (2*Geometry.theta-1) d cap delta p ≤ Geometry.theta-fee) :
    rowAt bs (2*beta-1) d cap delta p-beta ≤ -fee-(24/25)*(beta-Geometry.theta) := by
  have ha : (7/10:ℝ) ≤ 2*Geometry.theta-1 := by
    linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds.theta_bounds.1]
  have hak : 2*Geometry.theta-1 ≤ 2*beta-1 := by linarith
  have hg := QRH.Record12518109Return.envelope_gap bs ha hak
    (show 0 ≤ delta ∧ delta ≤ 5/6 by constructor <;> linarith [hdelta.1,hdelta.2]) hp
  have hm := mul_le_mul_of_nonneg_left hg (show 0 ≤ (3/4:ℝ)*d by
    exact mul_nonneg (by norm_num) hd.1)
  have hn := mul_nonneg (sub_nonneg.mpr hd.2) (show 0 ≤ beta-Geometry.theta by linarith)
  unfold rowAt at hbase ⊢
  nlinarith only [hm,hn,hbase,le_of_lt hgap]

/-- The literal physical exponent ledger with the chosen positive fee. All
front, frequency, mass, count, profile and mesh costs remain in physicalLoss. -/
theorem physical_packet_with_fee (bs : List Branch) (D : BaselineData)
    (eps sigma affineError d a q cap fee : ℝ)
    (hgap : Geometry.theta < OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hfee : 0 < fee)
    (hkap : D.momentKappa = 2*OAI.SevenEighths.HeckeZeroSupremum.beta-1)
    (heps : 0 ≤ eps) (hsigma : 0 ≤ sigma) (haff : 0 ≤ affineError)
    (hbudget : 16*D.e+2*eps+3*sigma/4+affineError/4+8*D.t ≤
      (OAI.SevenEighths.HeckeZeroSupremum.beta-Geometry.theta)/4)
    (hd : d ∈ Icc (0:ℝ) 1) (ha : (51/100:ℝ) ≤ a) (hatop : a ≤ 7/8)
    (hq : 0 ≤ q ∧ q ≤ (2*a-1)/2)
    (hbase : rowAt bs (2*Geometry.theta-1) d cap (2*a-1) (q/(2*a-1)) ≤ Geometry.theta-fee) :
    numeratorExponent bs D.momentKappa d cap (2*a-1) (q/(2*a-1))+
      weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma affineError) ≤
      OAI.SevenEighths.HeckeZeroSupremum.beta+
        Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.signalShift-
        fee/2-(OAI.SevenEighths.HeckeZeroSupremum.beta-Geometry.theta)/2-D.t-kernelExponent a D.e := by
  have hdelta : 0 < 2*a-1 := by linarith
  have hdel : (2*a-1) ∈ Icc (0:ℝ) (3/4) := by constructor <;> linarith
  have hp : q/(2*a-1) ∈ Icc (0:ℝ) (1/2) :=
    ⟨div_nonneg hq.1 hdelta.le,(div_le_iff₀ hdelta).mpr (by linarith [hq.2])⟩
  have hl := physical_loss_bound D eps sigma affineError d (2*a-1)
    heps hsigma haff hd.2 hdel
  have hr := row_supremum_deficit bs hgap hd hdel hp hbase
  have hh := packet_certificate bs (physicalLoss D eps sigma affineError) hgap hfee
    (by linarith : rowAt bs (2*OAI.SevenEighths.HeckeZeroSupremum.beta-1) d cap
      (2*a-1) (q/(2*a-1))-OAI.SevenEighths.HeckeZeroSupremum.beta ≤
        -fee-(3/4)*(OAI.SevenEighths.HeckeZeroSupremum.beta-Geometry.theta))
    (by linarith : 16*D.e+weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma affineError)+D.t ≤
      (OAI.SevenEighths.HeckeZeroSupremum.beta-Geometry.theta)/4)
  rw [←hkap,show (1+(2*a-1))/2 = a by ring] at hh
  linarith

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.row_supremum_deficit
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.physical_packet_with_fee
