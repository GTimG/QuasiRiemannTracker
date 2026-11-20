/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
All actual current-exterior leaves use the same genuine paired source count. -/
import Candidate.C092.transport.PacketJoinPaddedPrice
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open QRH.Record1252270103Return
open QRH.Cycle090 QRH.Cycle092.Direct QRH.Coverage QRH.PhysicalCertificate
open QRH.Cycle092.SelectedNonfloor
namespace QRH.Cycle092.PacketJoin

lemma exterior_boxes_in_admission : Physical.exteriorBoxes.all
    (fun box=>decide (Box.Included box pairedAdmissionBox))=true := by decide +kernel

def pairedUpperAdmission (δ p : ℝ) : Prop :=
  (∃ box : Box,box∈pairedBoxes ∧ box.Contains (δ,p)) ∨
  ∃ leaf∈forestRecords qForest,leaf.route≠.mixed ∧ leaf.box.Contains (δ,p)

variable [Geometry.Parameters]
lemma paired_upper_available {δ p : ℝ} (had : pairedUpperAdmission δ p) :
    PacketJoinE49.Return.window.Available δ p := by
  rcases had with ⟨box,hm,hp⟩ | ⟨leaf,hm,hr,hp⟩
  · exact e49_box_available hm hp
  · have hb := Physical.actual_exterior_box hm (Physical.exterior_is_current hm hr)
    have hi := of_decide_eq_true (List.all_eq_true.mp exterior_boxes_in_admission leaf.box hb)
    have ha := Box.contains_of_included hi hp
    norm_num [PacketJoinE49.Return.ImprovedWindow.Available,PacketJoinE49.Return.window,
      pairedAdmissionBox,Box.Contains] at ha ⊢
    exact ⟨⟨ha.1,ha.2.1⟩,ha.2.2⟩

lemma paired_upper_row_price_padded {δ p d : ℝ} (had : pairedUpperAdmission δ p)
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper) (hell : Geometry.ell=Physical.ell)
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2)
    (hd : 0<d) (hdh : d≤Geometry.h+rowPad) :
    rowPrice δ p (PacketJoinE49.Return.valueI δ p) d sourceCost≤theta-1/125000000+2*rowPad := by
  rcases had with hbox | ⟨leaf,hm,hr,hbox⟩
  · obtain ⟨box,hb,hpbox⟩ := hbox
    exact e49_row_price_padded hb hpbox hh hh' hell hδ hδ' hp hp' hd hdh
  · have hav := paired_upper_available (Or.inr ⟨leaf,hm,hr,hbox⟩)
    have hc := Qrh.TwoSlot.AnchorContinuum.Contact.tangent_coefficient_bounds
    have hgeom : 0<Geometry.h := (by norm_num [hLower] : (0:ℝ)<hLower).trans_le hh
    have ht := Physical.all_currentExterior_price hm (Physical.exterior_is_current hm hr)
      hh hh' hbox hc.1.le hc.2.1.le hc.2.2.1.le hc.2.2.2.le (le_refl Geometry.h)
    have hy : Geometry.y=Geometry.h-2*Geometry.ell := by unfold Geometry.h;linarith [Geometry.x_add_y]
    have hcap := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hgeom
    have heq : rowPrice δ p (PacketJoinE49.Return.valueI δ p) Geometry.h sourceCost =
        Physical.price Geometry.h δ p PacketJoinE49.Return.line.g0 PacketJoinE49.Return.line.g1 Geometry.h := by
      unfold rowPrice Physical.price
      rw [hcap,hy,hell]
      congr 2
      unfold PacketJoinE49.Return.valueI PacketJoinE49.Return.NI PacketJoinE49.Return.JI
        PacketJoinE49.Return.UI PacketJoinE49.Return.kI pairedCount pairedN pairedJ pairedV pairedU pairedK
      congr 1
      ring
    change 1/125000000≤theta-Physical.price Geometry.h δ p
      PacketJoinE49.Return.line.g0 PacketJoinE49.Return.line.g1 Geometry.h at ht
    apply row_price_padded_of_top hδ hδ' hp hp' (e49_value_lower hav) (e49_value_upper hav) hgeom hd hdh
    rw [heq]
    linarith
end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.exterior_boxes_in_admission
#print axioms QRH.Cycle092.PacketJoin.paired_upper_row_price_padded
