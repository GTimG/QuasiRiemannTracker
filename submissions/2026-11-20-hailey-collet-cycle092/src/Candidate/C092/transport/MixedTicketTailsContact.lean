/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original PR141 tangent is the literal contact line enclosed by the receipt. -/
import Candidate.C092.transport.PacketJoinE49Window
import Candidate.C092.transport.TopActual
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace QRH.Cycle092.MixedTicketTails

 theorem actual_contact_root : QRH.RationalInterval.Contains QRH.ContactCertificate.alphaInterval Qrh.TwoSlot.AnchorContinuum.Contact.theta := by
  have h := Qrh.TwoSlot.AnchorContinuum.Contact.theta_isolated
  constructor
  · simpa only [QRH.ContactCertificate.alphaInterval,QRH.ContactCertificate.alphaLo,Qrh.TwoSlot.AnchorContinuum.Contact.lower,Rat.cast_div,Rat.cast_ofNat] using h.1.le
  · simpa only [QRH.ContactCertificate.alphaInterval,QRH.ContactCertificate.alphaHi,Qrh.TwoSlot.AnchorContinuum.Contact.upper,Rat.cast_div,Rat.cast_ofNat] using h.2.le

 theorem actual_contact_width : Qrh.TwoSlot.AnchorContinuum.Contact.width = QRH.ContactCertificate.wValue Qrh.TwoSlot.AnchorContinuum.Contact.theta := by rfl

 theorem actual_contact_slope : Qrh.TwoSlot.AnchorContinuum.Contact.exactLine.g1 = QRH.ContactCertificate.g1 Qrh.TwoSlot.AnchorContinuum.Contact.width := by
  change -Qrh.TwoSlot.AnchorContinuum.Contact.tangentSlope = _
  rw [Qrh.TwoSlot.AnchorContinuum.Contact.negative_slope_formula]
  have hw := Qrh.TwoSlot.AnchorContinuum.Contact.width_range
  have h0 : Qrh.TwoSlot.AnchorContinuum.Contact.width ≠ 0 := by linarith
  have h1 : 45*Qrh.TwoSlot.AnchorContinuum.Contact.width-14 ≠ 0 := by linarith
  have h2 : 15*Qrh.TwoSlot.AnchorContinuum.Contact.width-10 ≠ 0 := by linarith
  have h3 : Qrh.TwoSlot.AnchorContinuum.Contact.width-2/3 ≠ 0 := by linarith
  have h4 : 140-Qrh.TwoSlot.AnchorContinuum.Contact.width*660+Qrh.TwoSlot.AnchorContinuum.Contact.width^2*675 ≠ 0 := by
    have he : 140-Qrh.TwoSlot.AnchorContinuum.Contact.width*660+Qrh.TwoSlot.AnchorContinuum.Contact.width^2*675 =
        (45*Qrh.TwoSlot.AnchorContinuum.Contact.width-14)*(15*Qrh.TwoSlot.AnchorContinuum.Contact.width-10) := by ring
    rw [he];exact mul_ne_zero h1 h2
  have h5 : -2+Qrh.TwoSlot.AnchorContinuum.Contact.width*3 ≠ 0 := by linarith
  have h6 : -14+Qrh.TwoSlot.AnchorContinuum.Contact.width*45 ≠ 0 := by linarith
  norm_num [QRH.ContactCertificate.g1,QRH.ContactCertificate.g1Expr,QRH.ContactCertificate.radialExpr,QRH.ContactCertificate.interceptExpr,QRH.RationalInterval.value]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  <;> ring_nf
  <;> field_simp [h0,h1,h2,h3,h4,h5,h6]
  <;> ring

 theorem actual_contact_intercept : Qrh.TwoSlot.AnchorContinuum.Contact.exactLine.g0 = QRH.ContactCertificate.g0 Qrh.TwoSlot.AnchorContinuum.Contact.width := by
  change Qrh.TwoSlot.AnchorContinuum.Contact.tangentIntercept = _
  rw [Qrh.TwoSlot.AnchorContinuum.Contact.tangentIntercept_formula]
  have hw := Qrh.TwoSlot.AnchorContinuum.Contact.width_range
  have h0 : Qrh.TwoSlot.AnchorContinuum.Contact.width ≠ 0 := by linarith
  have h1 : 45*Qrh.TwoSlot.AnchorContinuum.Contact.width-14 ≠ 0 := by linarith
  have h2 : 15*Qrh.TwoSlot.AnchorContinuum.Contact.width-10 ≠ 0 := by linarith
  have h3 : Qrh.TwoSlot.AnchorContinuum.Contact.width-2/3 ≠ 0 := by linarith
  have h4 : 140-Qrh.TwoSlot.AnchorContinuum.Contact.width*660+Qrh.TwoSlot.AnchorContinuum.Contact.width^2*675 ≠ 0 := by
    have he : 140-Qrh.TwoSlot.AnchorContinuum.Contact.width*660+Qrh.TwoSlot.AnchorContinuum.Contact.width^2*675 =
        (45*Qrh.TwoSlot.AnchorContinuum.Contact.width-14)*(15*Qrh.TwoSlot.AnchorContinuum.Contact.width-10) := by ring
    rw [he];exact mul_ne_zero h1 h2
  have h5 : -2+Qrh.TwoSlot.AnchorContinuum.Contact.width*3 ≠ 0 := by linarith
  have h6 : -14+Qrh.TwoSlot.AnchorContinuum.Contact.width*45 ≠ 0 := by linarith
  norm_num [QRH.ContactCertificate.g0,QRH.ContactCertificate.g0Expr,QRH.ContactCertificate.g1Expr,QRH.ContactCertificate.radialExpr,QRH.ContactCertificate.interceptExpr,QRH.RationalInterval.value]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  <;> ring_nf
  <;> field_simp [h0,h1,h2,h3,h4,h5,h6]
  <;> ring

 theorem actual_tangent_contact : Top.ContactBounds Qrh.TwoSlot.AnchorContinuum.Contact.exactLine.g0 Qrh.TwoSlot.AnchorContinuum.Contact.exactLine.g1 := by
  rw [actual_contact_intercept,actual_contact_slope,actual_contact_width]
  exact Top.actual_contact actual_contact_root
end QRH.Cycle092.MixedTicketTails
#print axioms QRH.Cycle092.MixedTicketTails.actual_tangent_contact
