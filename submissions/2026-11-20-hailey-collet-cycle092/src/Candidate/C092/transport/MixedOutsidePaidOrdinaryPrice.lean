/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
All original ordinary-high source alternatives pay the original old ticket. -/
import Candidate.C092.transport.MixedOutsidePaidOrdinary
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace QRH.Cycle092.MixedOutsidePaid
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.RawTicket
open QRH.Cycle092.SelectedNonfloor QRH.Cycle092.PacketJoin QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.PacketJoinE49 QRH.PositiveGap.Return QRH.Record1252270103Return
variable [Geometry.Parameters]

theorem original_ordinary_high_price_paid {r:Row} (hr:r∈rows) {δ p d:ℝ}
    (hpbox:r.box.Contains (δ,p))
    (hh:hLower≤Geometry.h) (hh':Geometry.h≤hUpper) (hell:Geometry.ell=Physical.ell)
    (hd:originalDlow r≤d) (hdh:d≤Geometry.h+rowPad) :
    rowPrice δ p (ordinaryHighR δ p) d sourceCost<QRH.Cycle090.theta-8*oldFee+2*rowPad := by
  have hδp:=original_point_bounds hr hpbox
  have pay (R gap:ℝ) (hg:gap∈continuationGaps r.box.vLo r.box.vHi tHi)
      (hR:R≤1-δ*(coarseCp r+gap)) : rowPrice δ p R d sourceCost<QRH.Cycle090.theta-8*oldFee+2*rowPad :=
    original_continuation_price_paid hr hpbox hh hh' hell hd hdh hg hR
  have hfull:rowPrice δ p (1-(9/10)*δ) d sourceCost<QRH.Cycle090.theta-8*oldFee+2*rowPad:=by
    apply pay _ (9/10-coarseCp r)
    · norm_num [continuationGaps,coarseCp]
    · ring_nf;exact le_rfl
  have hnat:rowPrice δ p (1-δ*((1-(9/2)*(27/1000))+2*p*(27/1000))) d sourceCost<QRH.Cycle090.theta-8*oldFee+2*rowPad:=by
    apply pay _ ((1-(9/2)*(27/1000))+2*(r.box.vLo:ℝ)*(27/1000)-coarseCp r)
    · norm_num [continuationGaps,coarseCp]
    · have hm:=mul_le_mul_of_nonneg_left hpbox.2.2.1 hδp.1
      nlinarith only [hm]
  have hcap:rowPrice δ p (1-δ*anchorTop-2*δ*p*(countCap-1/10000000)) d sourceCost<QRH.Cycle090.theta-8*oldFee+2*rowPad:=by
    apply pay _ (311/400+2*(r.box.vLo:ℝ)*(3/20-1/10000000)-coarseCp r)
    · norm_num [continuationGaps,coarseCp]
    · have hm:=mul_le_mul_of_nonneg_left hpbox.2.2.1 hδp.1
      norm_num [anchorTop,countCap]
      nlinarith only [hm]
  have haff:rowPrice δ p (1-δ*anchorTop-2*δ*p*(countCB-anchorTop)/countCL) d sourceCost<QRH.Cycle090.theta-8*oldFee+2*rowPad:=by
    apply pay _ (311/400+2*(r.box.vLo:ℝ)*((1-1/1000000000000)-311/400)/(2+1/100000000000)-coarseCp r)
    · norm_num [continuationGaps,coarseCp]
    · have hm:=mul_le_mul_of_nonneg_left hpbox.2.2.1 hδp.1
      norm_num [anchorTop,countCB,countCL]
      nlinarith only [hm]
  unfold ordinaryHighR plainCurve
  rw [max_def]
  split_ifs
  · rw [max_def]
    split_ifs
    · exact hfull
    · exact hnat
  · rw [max_def]
    split_ifs
    · convert haff using 1 <;> ring
    · convert hcap using 1 <;> ring

 theorem original_ordinary_high_price_errors_paid {r:Row} (hr:r∈rows) {δ p d loss moment mass fee:ℝ}
    (hpbox:r.box.Contains (δ,p))
    (hh:hLower≤Geometry.h) (hh':Geometry.h≤hUpper) (hell:Geometry.ell=Physical.ell)
    (hd:originalDlow r≤d) (hdh:d≤Geometry.h+rowPad)
    (hbudget:d*(3*loss/4+moment/4+mass)+fee+2*rowPad≤7*oldFee) :
    rowPrice δ p (ordinaryHighR δ p+loss) d sourceCost+d*(moment/4+mass)+fee≤QRH.Cycle090.theta-oldFee := by
  have hp:=original_ordinary_high_price_paid hr hpbox hh hh' hell hd hdh
  unfold rowPrice at hp ⊢
  nlinarith only [hp,hbudget]
end QRH.Cycle092.MixedOutsidePaid
#print axioms QRH.Cycle092.MixedOutsidePaid.original_ordinary_high_price_paid
