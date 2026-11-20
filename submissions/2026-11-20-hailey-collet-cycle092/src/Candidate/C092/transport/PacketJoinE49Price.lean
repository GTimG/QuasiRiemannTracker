/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native direct certificate at the actual conductor, with explicit source/count fees. -/
import Candidate.C092.transport.PacketJoinMean
import Candidate.C092.transport.PacketJoinE49Window
import Candidate.C092.transport.DirectPairedAdmission
import Candidate.C092.transport.SelectedNonfloorPrice
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open QRH.Record1252270103Return
open QRH.Cycle090 QRH.Cycle092.Direct QRH.Cycle092.DirectCount
open QRH.Cycle092.SelectedNonfloor QRH.Coverage
namespace QRH.Cycle092.PacketJoin
variable [Geometry.Parameters]


lemma e49_box_available {box : Box} (hm : box∈pairedBoxes) {δ p : ℝ}
    (hpbox : box.Contains (δ,p)) : PacketJoinE49.Return.window.Available δ p := by
  have hi := of_decide_eq_true (List.all_eq_true.mp pairedBoxes_in_admission box hm)
  have ha := QRH.PhysicalCertificate.Box.contains_of_included hi hpbox
  norm_num [PacketJoinE49.Return.ImprovedWindow.Available,PacketJoinE49.Return.window,
    pairedAdmissionBox,Box.Contains] at ha ⊢
  exact ⟨⟨ha.1,ha.2.1⟩,ha.2.2⟩

lemma e49_value_lower {δ p : ℝ}
    (hav : PacketJoinE49.Return.window.Available δ p) :
    1-δ≤PacketJoinE49.Return.valueI δ p := by
  have hl := PacketJoinE49.Return.long_identity δ p (PacketJoinE49.Return.hJ hav.1 hav.2).ne'
  have hc := PacketJoinE49.Return.window.cutoff_bounds hav.1 hav.2
  change 1≤PacketJoinE49.Return.cutoffI δ p ∧ PacketJoinE49.Return.cutoffI δ p≤3/2 at hc
  have hdhi := hav.1.2
  change δ≤(15/32:ℝ) at hdhi
  have hm := mul_nonneg (show (0:ℝ)≤5/6-δ by linarith) (show 0≤PacketJoinE49.Return.cutoffI δ p-1 by linarith)
  linarith

theorem e49_row_price_le_top {δ p D : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2)
    (hav : PacketJoinE49.Return.window.Available δ p)
    (hD : 0<D) (hDh : D≤Geometry.h) :
    rowPrice δ p (PacketJoinE49.Return.valueI δ p) D sourceCost ≤
      rowPrice δ p (PacketJoinE49.Return.valueI δ p) Geometry.h sourceCost := by
  have hh : 0<Geometry.h := hD.trans_le hDh
  have hcD := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hD
  have hch := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hh
  have hcap := cappedCapacity_increment_le physicalCap_admissible.1.le allowances_pos.1.le hDh (y:=Geometry.y)
  have hr := e49_value_lower hav
  have hdp : 0≤δ*p := mul_nonneg hδ hp
  have hdphi : δ*p≤3/8 := by nlinarith [mul_le_mul_of_nonneg_left hp' hδ]
  have hc : 0≤3*PacketJoinE49.Return.valueI δ p/4-9/100-δ*p*physicalCap/2 := by
    norm_num [physicalCap]
    nlinarith
  have hweight := mul_le_mul_of_nonneg_left hcap hdp
  have hnonneg := mul_nonneg hc (sub_nonneg.mpr hDh)
  unfold rowPrice
  rw [hcD,hch]
  nlinarith


lemma e49_row_price_of_box {box : Box} (hm : box∈pairedBoxes)
    {δ p d : ℝ} (hpbox : box.Contains (δ,p))
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper)
    (hell : Geometry.ell=Physical.ell)
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2)
    (hd : 0<d) (hdh : d≤Geometry.h) :
    rowPrice δ p (PacketJoinE49.Return.valueI δ p) d sourceCost≤theta-1/125000000 := by
  have hc := Qrh.TwoSlot.AnchorContinuum.Contact.tangent_coefficient_bounds
  have hb := certified_paired_top hm hh hh' hpbox hc.1.le hc.2.1.le hc.2.2.1.le hc.2.2.2.le
  have hgeom : 0<Geometry.h := hd.trans_le hdh
  have hy : Geometry.y=Geometry.h-2*Geometry.ell := by
    unfold Geometry.h
    linarith [Geometry.x_add_y]
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
    PacketJoinE49.Return.line.g0 PacketJoinE49.Return.line.g1 Geometry.h at hb
  have hm' := e49_row_price_le_top hδ hδ' hp hp' (e49_box_available hm hpbox) hd hdh
  rw [heq] at hm'
  linarith

end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.e49_row_price_of_box
