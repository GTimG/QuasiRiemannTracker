/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual Q1 row budget pays native large-count and all-long subclasses. -/
import Candidate.C092.transport.MixedUpperFinalAdmission
import Candidate.C092.transport.PacketFinalPower
import Candidate.C092.transport.ActualMixedPricePadded
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed QRH.Cycle092.RawTicket
open QRH.Cycle092.MixedTicketTails QRH.Cycle092.PacketJoinE49
open QRH.Record1252270103Return
local notation "contact" => Qrh.TwoSlot.AnchorContinuum.Contact.theta

lemma count_value_eq (δ p : ℝ) :
    Return.valueI δ p=pairedCount δ p Return.line.g0 Return.line.g1 := by
  unfold Return.valueI Return.NI Return.JI Return.UI Return.kI
    pairedCount pairedN pairedJ pairedV pairedU pairedK
  congr 1 <;> ring

/-- The full original Q1 excess is paid by a genuine count improvement of
4q0/3, with q0 equal to its actual row budget. Only scalar arithmetic is
assumed here; the source count suppliers discharge R separately. -/
theorem large_count_price_paid (h : ℝ) (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    {r : Row} (hr : r∈rows) {δ p d R loss moment mass fee : ℝ}
    (hp : r.box.Contains (δ,p)) (hd : 0<d) (hdh : d ≤ h+rowPad)
    (hR : R ≤ Return.valueI δ p-4*(rowBudget r.B:ℝ)/3+loss)
    (hbudget : d*(3*loss/4+moment/4+mass)+fee+rowPad ≤ 1/2000000000000) :
    @SelectedNonfloor.rowPrice (ActualGeometry.parameters h hh hh') δ p R d sourceCost+
      d*(moment/4+mass)+fee ≤ theta-1/2000000000000 := by
  letI := ActualGeometry.parameters h hh hh'
  have hb:=ActualMixedPrice.padded_debit hr hh hh' hp actual_contact_root hd.le hdh
  have hraw : Physical.price h δ p (QRH.ContactCertificate.g0 (QRH.ContactCertificate.wValue contact))
      (QRH.ContactCertificate.g1 (QRH.ContactCertificate.wValue contact)) d-theta+inwardDebit ≤
      d*(rowBudget r.B:ℝ)+rowPad := by
    apply le_trans (le_max_right (0:ℝ) _) hb
  have heq : SelectedNonfloor.rowPrice δ p (Return.valueI δ p) d sourceCost=
      Physical.price h δ p (QRH.ContactCertificate.g0 (QRH.ContactCertificate.wValue contact))
        (QRH.ContactCertificate.g1 (QRH.ContactCertificate.wValue contact)) d := by
    rw [count_value_eq,SelectedNonfloor.row_price_at_Q h hh hh' δ p Return.line.g0 Return.line.g1 d hd,
      actual_contact_intercept,actual_contact_slope,actual_contact_width]
  have hm:=mul_le_mul_of_nonneg_left hR (show 0 ≤ 3*d/4 by positivity)
  unfold SelectedNonfloor.rowPrice at hm heq ⊢
  norm_num [inwardDebit] at hraw
  nlinarith only [hraw,heq,hm,hbudget]

#print axioms count_value_eq
#print axioms large_count_price_paid
end
end QRH.Cycle092.MixedUpperFinal
