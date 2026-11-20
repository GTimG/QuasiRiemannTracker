/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original large-dilation ticket pays the actual source count price. -/
import Candidate.C092.transport.MixedTicketTailsRawActual
import Candidate.C092.transport.MixedTicketTailsContact
import Candidate.C092.transport.PacketJoinPaddedPrice
import Candidate.C092.transport.ActualMixedPrice
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.RawTicket
open QRH.Cycle092.SelectedNonfloor QRH.Cycle092.PacketJoin
variable [QRH.Record1252270103Return.Geometry.Parameters]
open QRH.Record1252270103Return

def originalDebit (r : Row) := oldDebit r.box.uLo r.box.uHi r.box.vLo r.box.vHi (originalSep r)
def originalDlow (r : Row) := Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi (originalSep r)
def originalVcut (r : Row) := funded (originalDebit r) (originalDlow r*(r.box.uLo:ℝ)/4)

lemma original_e49_available {r : Row} (hr : r∈rows) {δ p : ℝ}
    (hpbox : r.box.Contains (δ,p)) : PacketJoinE49.Return.window.Available δ p := by
  have hg := (ActualMixedPrice.geometry hr hpbox).1
  norm_num [Direct.pairedAdmissionBox,QRH.Coverage.Box.Contains] at hg
  norm_num [PacketJoinE49.Return.ImprovedWindow.Available,PacketJoinE49.Return.window]
  exact ⟨⟨hg.1,hg.2.1⟩,⟨hg.2.2.1,hg.2.2.2⟩⟩

lemma original_point_bounds {r : Row} (hr : r∈rows) {δ p : ℝ}
    (hpbox : r.box.Contains (δ,p)) : 0≤δ ∧ δ≤3/4 ∧ 0≤p ∧ p≤1/2 := by
  have hg := (ActualMixedPrice.geometry hr hpbox).1
  norm_num [Direct.pairedAdmissionBox,QRH.Coverage.Box.Contains] at hg
  exact ⟨by linarith [hg.1],by linarith [hg.2.1],by linarith [hg.2.2.1],hg.2.2.2⟩

/-- The exact source line, not an assumed numerical strengthening, is used. -/
lemma original_actual_top_debit {r : Row} (hr : r∈rows) {δ p : ℝ}
    (hpbox : r.box.Contains (δ,p))
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper)
    (hell : Geometry.ell=Physical.ell) :
    rowPrice δ p (PacketJoinE49.Return.valueI δ p) Geometry.h sourceCost ≤ theta+originalDebit r := by
  have hb := Top.top_budget (List.all_eq_true.mp Top.all_rows_checked r hr)
    hh hh' hpbox actual_tangent_contact
  have hgeom : 0<Geometry.h := (by norm_num [hLower] : (0:ℝ)<hLower).trans_le hh
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
  have hraw := actual_original_debit_bridge hr
  rw [heq]
  change _ ≤ theta+originalDebit r
  change _-theta≤(r.B:ℝ) at hb
  change (r.B:ℝ)≤originalDebit r at hraw
  linarith

lemma original_actual_debit_padded {r : Row} (hr : r∈rows) {δ p d : ℝ}
    (hpbox : r.box.Contains (δ,p))
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper)
    (hell : Geometry.ell=Physical.ell) (hd : 0<d) (hdh : d≤Geometry.h+rowPad) :
    rowPrice δ p (PacketJoinE49.Return.valueI δ p) d sourceCost ≤ theta+originalDebit r+2*rowPad := by
  obtain ⟨hδ,hδ',hp,hp'⟩ := original_point_bounds hr hpbox
  have hav := original_e49_available hr hpbox
  have htop := original_actual_top_debit hr hpbox hh hh' hell
  have hh0 : 0<Geometry.h := (by norm_num [hLower] : (0:ℝ)<hLower).trans_le hh
  simpa only [sub_neg_eq_add] using row_price_padded_of_top hδ hδ' hp hp'
    (e49_value_lower hav) (e49_value_upper hav) hh0 hd hdh (margin:= -originalDebit r) (by linarith)

lemma original_vcut_nonneg {r : Row} (hr : r∈rows) : 0≤originalVcut r := by
  have hD := (every_original_band hr (originalSep r)).2.1
  have ha := (row_endpoint_hull hr).1
  have hD0 : 0<originalDlow r := (by norm_num [Dmin] : (0:ℝ)<Dmin).trans_le hD
  have ha0 : 0<(r.box.uLo:ℝ) := (by norm_num [dLo] : (0:ℝ)<dLo).trans_le ha.1
  have hq : 0≤(max 0 (originalDebit r)+10*oldFee)/(originalDlow r*(r.box.uLo:ℝ)/4) := by
    apply div_nonneg
    · have hm := le_max_left (0:ℝ) (originalDebit r)
      norm_num [oldFee];linarith
    · positivity
  exact hq.trans (rounding (x:= (max 0 (originalDebit r)+10*oldFee)/(originalDlow r*(r.box.uLo:ℝ)/4))
    (n:=10^(9:ℕ)) (by norm_num)).2.2.1

/-- Every literal original terminal pays large dilation, including the actual
upper-conductor padding. No original debit/price inequality is assumed. -/
theorem original_large_price_paid {r : Row} (hr : r∈rows) {δ p d : ℝ}
    (hpbox : r.box.Contains (δ,p))
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper)
    (hell : Geometry.ell=Physical.ell)
    (hd : originalDlow r≤d) (hdh : d≤Geometry.h+rowPad) :
    rowPrice δ p (PacketJoinE49.Return.valueI δ p) d sourceCost-
      d*δ*originalVcut r/4 < theta-8*oldFee+2*rowPad := by
  have hD := (every_original_band hr (originalSep r)).2.1
  have ha := (row_endpoint_hull hr).1
  have hD0 : 0<originalDlow r := (by norm_num [Dmin] : (0:ℝ)<Dmin).trans_le hD
  have ha0 : 0<(r.box.uLo:ℝ) := (by norm_num [dLo] : (0:ℝ)<dLo).trans_le ha.1
  have hd0 : 0<d := hD0.trans_le hd
  have hδ : (r.box.uLo:ℝ)≤δ := hpbox.1
  have hfund := ceil_funds_original_fee (debit:=originalDebit r)
    (show 0<originalDlow r*(r.box.uLo:ℝ)/4 by positivity)
  change 8*oldFee<originalDlow r*(r.box.uLo:ℝ)/4*originalVcut r-originalDebit r at hfund
  have hprod := mul_le_mul hd hδ ha0.le hd0.le
  have hgain := mul_le_mul_of_nonneg_right hprod (original_vcut_nonneg hr)
  have hprice := original_actual_debit_padded hr hpbox hh hh' hell hd0 hdh
  nlinarith only [hfund,hgain,hprice]
end QRH.Cycle092.MixedTicketTails
#print axioms QRH.Cycle092.MixedTicketTails.original_large_price_paid
