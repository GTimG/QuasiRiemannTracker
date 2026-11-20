/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual E49 count price pays every original small-conductor exit. -/
import Candidate.C092.transport.MixedOutsidePaidPrice
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace QRH.Cycle092.MixedOutsidePaid
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.RawTicket
open QRH.Cycle092.SelectedNonfloor QRH.Cycle092.PacketJoin QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.PacketJoinE49 QRH.Record1252270103Return
variable [Geometry.Parameters]

 theorem original_small_conductor_price_paid {r:Row} (hr:r∈rows) {δ p d:ℝ}
    (hpbox:r.box.Contains (δ,p))
    (hh:hLower≤Geometry.h) (hh':Geometry.h≤hUpper) (hell:Geometry.ell=Physical.ell)
    (hd:0<d) (hdlo:d≤originalDlow r) :
    rowPrice δ p (Return.valueI δ p) d sourceCost<theta-8*oldFee := by
  have hav:=original_e49_available hr hpbox
  obtain ⟨hδ,hδhi,hp,hphi⟩:=original_point_bounds hr hpbox
  have hrlo:=e49_value_lower hav
  have hb:=row_endpoint_hull hr
  have hband:=every_original_band hr (originalSep r)
  have hdhi:d≤Geometry.h:=hdlo.trans (hband.2.2.trans hh)
  have hh0:=hd.trans_le hdhi
  have hs0:0<sourceSlope (r.box.uHi:ℝ):=(by norm_num [slopeMin,dHi] : (0:ℝ)<slopeMin).trans_le (source_slope_lower hb.2.1.2)
  have hfund:=ceil_funds_original_fee (debit:=originalDebit r) hs0
  change 8*oldFee<sourceSlope (r.box.uHi:ℝ)*funded (originalDebit r) (sourceSlope (r.box.uHi:ℝ))-originalDebit r at hfund
  have hdistance:funded (originalDebit r) (sourceSlope (r.box.uHi:ℝ))≤Geometry.h-d:=by
    change d≤hLower-funded (originalDebit r) (sourceSlope (r.box.uHi:ℝ)) at hdlo
    linarith only [hdlo,hh]
  have hgain:=mul_le_mul_of_nonneg_left hdistance hs0.le
  have hdp:=mul_nonneg hδ hp
  have hδb:δ≤(r.box.uHi:ℝ):=hpbox.2.1
  have hdpb:δ*p≤(r.box.uHi:ℝ)/2:=by nlinarith [mul_le_mul_of_nonneg_left hphi hδ]
  have hcoef:sourceSlope (r.box.uHi:ℝ)≤3*Return.valueI δ p/4-9/100-δ*p*physicalCap/2:=by
    norm_num [sourceSlope,physicalCap]
    linarith only [hrlo,hδb,hdpb]
  have hcoefgain:=mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hdhi)
  have hcD:=Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hd
  have hch:=Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hh0
  have hcap:=cappedCapacity_increment_le physicalCap_admissible.1.le allowances_pos.1.le hdhi (y:=Geometry.y)
  have hweight:=mul_le_mul_of_nonneg_left hcap hdp
  have hprice:=original_actual_top_debit hr hpbox hh hh' hell
  unfold rowPrice at hprice ⊢
  rw [hcD,hch] at *
  nlinarith only [hprice,hweight,hcoefgain,hgain,hfund]

 theorem original_small_conductor_price_errors_paid {r:Row} (hr:r∈rows) {δ p d loss moment mass fee:ℝ}
    (hpbox:r.box.Contains (δ,p))
    (hh:hLower≤Geometry.h) (hh':Geometry.h≤hUpper) (hell:Geometry.ell=Physical.ell)
    (hd:0<d) (hdlo:d≤originalDlow r)
    (hbudget:d*(3*loss/4+moment/4+mass)+fee≤7*oldFee) :
    rowPrice δ p (Return.valueI δ p+loss) d sourceCost+d*(moment/4+mass)+fee≤theta-oldFee := by
  have hp:=original_small_conductor_price_paid hr hpbox hh hh' hell hd hdlo
  unfold rowPrice at hp ⊢
  nlinarith only [hp,hbudget]
end QRH.Cycle092.MixedOutsidePaid
#print axioms QRH.Cycle092.MixedOutsidePaid.original_small_conductor_price_paid
