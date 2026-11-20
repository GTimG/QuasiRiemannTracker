/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original continuation fees applied to the genuine inverse-high source. -/
import Candidate.C092.transport.MixedOutsidePaidInverse
import Candidate.C092.transport.RawTicketAdmission
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace QRH.Cycle092.MixedOutsidePaid
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.RawTicket
open QRH.Cycle092.SelectedNonfloor QRH.Cycle092.PacketJoin
open QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.PacketJoinE49.Return
open QRH.Record1252270103Return
variable [Geometry.Parameters]

def coarseCp (r:Row):ℝ := (r.box.vHi:ℝ)*(1+2*(5805913/100000000))+
  (1-(r.box.vLo:ℝ)*(1+2*(3799809/50000000)))*2*tHi/3

def inverseGap (r:Row):ℝ := 311/400+(r.box.vLo:ℝ)*(1-311/400)-coarseCp r

lemma actual_cutoff_eq (δ p:ℝ) (hJ0:JI δ p≠0) : cutoffI δ p=pairedCrossing δ p line.g0 line.g1 := by
  have he:pairedJ δ p line.g1=JI δ p:=by
    unfold JI kI pairedJ pairedV pairedK
    ring
  unfold pairedCrossing
  rw [he]
  unfold cutoffI TI UI pairedU
  field_simp

lemma original_coarse_value {r:Row} (hr:r∈rows) {δ p:ℝ}
    (hpbox:r.box.Contains (δ,p)) : 1-δ*coarseCp r≤valueI δ p := by
  have hav:=original_e49_available hr hpbox
  have hδp:=original_point_bounds hr hpbox
  have hJ0:=hJ hav.1 hav.2
  have hk0:=hk hav.1 hav.2
  have hc:=actual_crossing_bounds hr hpbox actual_contact_root
  rw [←actual_contact_width,←actual_contact_intercept,←actual_contact_slope,←actual_cutoff_eq δ p hJ0.ne'] at hc
  have hcross:crossingI δ p=2*cutoffI δ p/3:=by unfold crossingI cutoffI;ring
  have hcrosshi:crossingI δ p≤2*tHi/3:=by rw [hcross];linarith [hc.2]
  have h0:=QRH.ContactCertificate.g0_receipt_sound actual_contact_root
  have h1:=QRH.ContactCertificate.g1_receipt_sound actual_contact_root
  have hb:=receipt_original_bounds
  have hg0:line.g0≤5805913/100000000:=by
    rw [actual_contact_intercept,actual_contact_width]
    exact h0.2.trans hb.2.2.2.1
  have hg1:(3799809/50000000:ℝ)≤line.g1:=by
    rw [actual_contact_slope,actual_contact_width]
    exact hb.2.2.2.2.1.trans h1.1
  have hleft:p*(1+2*line.g0)≤(r.box.vHi:ℝ)*(1+2*(5805913/100000000)):=by
    have hh:=mul_le_mul_of_nonneg_left hg0 hδp.2.2.1
    nlinarith only [hh,hpbox.2.2.2]
  have hcoef: kI p≤1-(r.box.vLo:ℝ)*(1+2*(3799809/50000000)):=by
    have hh:=mul_le_mul_of_nonneg_left hg1 hδp.2.2.1
    unfold kI
    nlinarith only [hh,hpbox.2.2.1]
  have hrhs0:0≤1-(r.box.vLo:ℝ)*(1+2*(3799809/50000000)):=hk0.le.trans hcoef
  have hc0:0≤cutoffI δ p:=(by norm_num [tLo] : (0:ℝ)≤tLo).trans hc.1
  have hprod:=mul_le_mul hcoef hcrosshi (by rw [hcross]; positivity) hrhs0
  have hid:=inverse_identity δ p hJ0.ne'
  have hbkt:p*(1+2*line.g0)+kI p*crossingI δ p≤coarseCp r:=by
    unfold coarseCp
    linarith only [hleft,hprod]
  have hm:=mul_le_mul_of_nonneg_left hbkt hδp.1
  unfold kI at hm
  linarith only [hm,hid]

lemma original_inverse_gap_paid {r:Row} (hr:r∈rows) :
    8*oldFee<3*originalDlow r*(r.box.uLo:ℝ)*inverseGap r/4-originalDebit r := by
  have hf:=every_original_continuation hr (originalSep r) tHi ⟨by norm_num [tHi],le_rfl⟩
  exact hf (inverseGap r) (by simp [continuationGaps,inverseGap,coarseCp])

lemma original_inverse_gap_pos {r:Row} (hr:r∈rows) : 0 ≤ inverseGap r := by
  have he:=row_endpoint_hull hr
  have h:=continuation_gaps_uniform he.2.2.1 he.2.2.2 ⟨by norm_num [tHi],le_rfl⟩
    (inverseGap r) (by simp [continuationGaps,inverseGap,coarseCp])
  linarith

/-- The original inverse-high continuation pays the old fee at actual conductor
D, including its original upper padding. -/
theorem original_inverse_high_price_paid {r:Row} (hr:r∈rows) {δ p d:ℝ}
    (hpbox:r.box.Contains (δ,p))
    (hh:hLower≤Geometry.h) (hh':Geometry.h≤hUpper) (hell:Geometry.ell=Physical.ell)
    (hd:originalDlow r≤d) (hdh:d≤Geometry.h+rowPad) :
    rowPrice δ p (inverseHighR δ p) d sourceCost<theta-8*oldFee+2*rowPad := by
  have hδp:=original_point_bounds hr hpbox
  have hD:0<originalDlow r := (by norm_num [Dmin] : (0:ℝ)<Dmin).trans_le
    (every_original_band hr (originalSep r)).2.1
  have hd0:=hD.trans_le hd
  have ha:0<(r.box.uLo:ℝ):=(by norm_num [dLo] : (0:ℝ)<dLo).trans_le (row_endpoint_hull hr).1.1
  have hlow:=original_coarse_value hr hpbox
  have hgap:=original_inverse_gap_paid hr
  have hgap0:=original_inverse_gap_pos hr
  have hgain:=mul_le_mul_of_nonneg_right (mul_le_mul hd hpbox.1 ha.le hd0.le) hgap0
  have hprice:=original_actual_debit_padded hr hpbox hh hh' hell hd0 hdh
  have hbr:(r.box.vLo:ℝ)*(1-311/400)≤p*(1-311/400):=by linarith only [hpbox.2.2.1]
  have hR:inverseHighR δ p≤valueI δ p-δ*inverseGap r:=by
    have hmul:=mul_le_mul_of_nonneg_left hbr hδp.1
    unfold inverseHighR QRH.Cycle092.PacketJoinE49.anchorTop inverseGap at *
    nlinarith only [hlow,hmul]
  have hmul:=mul_le_mul_of_nonneg_left hR hd0.le
  unfold rowPrice at hprice ⊢
  nlinarith only [hmul,hprice,hgap,hgain]
/-- Exact error allocation after the genuine native count; the original ticket
pays seven old fees and retains the eighth one. -/
theorem original_inverse_high_price_errors_paid {r:Row} (hr:r∈rows) {δ p d loss moment mass fee:ℝ}
    (hpbox:r.box.Contains (δ,p))
    (hh:hLower≤Geometry.h) (hh':Geometry.h≤hUpper) (hell:Geometry.ell=Physical.ell)
    (hd:originalDlow r≤d) (hdh:d≤Geometry.h+rowPad)
    (hbudget:d*(3*loss/4+moment/4+mass)+fee+2*rowPad≤7*oldFee) :
    rowPrice δ p (inverseHighR δ p+loss) d sourceCost+d*(moment/4+mass)+fee≤theta-oldFee := by
  have hp:=original_inverse_high_price_paid hr hpbox hh hh' hell hd hdh
  unfold rowPrice at hp ⊢
  nlinarith only [hp,hbudget]

/-- A literal original continuation gap pays any proved count exponent below
its coarse envelope. The gap fee is supplied by the original checked rows. -/
theorem original_continuation_price_paid {r:Row} (hr:r∈rows) {δ p d R gap:ℝ}
    (hpbox:r.box.Contains (δ,p))
    (hh:hLower≤Geometry.h) (hh':Geometry.h≤hUpper) (hell:Geometry.ell=Physical.ell)
    (hd:originalDlow r≤d) (hdh:d≤Geometry.h+rowPad)
    (hg:gap∈continuationGaps r.box.vLo r.box.vHi tHi)
    (hR:R≤1-δ*(coarseCp r+gap)) :
    rowPrice δ p R d sourceCost<theta-8*oldFee+2*rowPad := by
  have hδp:=original_point_bounds hr hpbox
  have hD:0<originalDlow r := (by norm_num [Dmin] : (0:ℝ)<Dmin).trans_le
    (every_original_band hr (originalSep r)).2.1
  have hd0:=hD.trans_le hd
  have ha:0<(r.box.uLo:ℝ):=(by norm_num [dLo] : (0:ℝ)<dLo).trans_le (row_endpoint_hull hr).1.1
  have hlow:=original_coarse_value hr hpbox
  have hgap:=every_original_continuation hr (originalSep r) tHi ⟨by norm_num [tHi],le_rfl⟩ gap hg
  have he:=row_endpoint_hull hr
  have hgap0:0≤gap:=by
    have h:=continuation_gaps_uniform he.2.2.1 he.2.2.2 ⟨by norm_num [tHi],le_rfl⟩ gap hg
    linarith
  have hgain:=mul_le_mul_of_nonneg_right (mul_le_mul hd hpbox.1 ha.le hd0.le) hgap0
  have hprice:=original_actual_debit_padded hr hpbox hh hh' hell hd0 hdh
  have hR':R≤valueI δ p-δ*gap:=by nlinarith only [hlow,hR]
  have hmul:=mul_le_mul_of_nonneg_left hR' hd0.le
  unfold rowPrice at hprice ⊢
  change 8*oldFee<3*originalDlow r*(r.box.uLo:ℝ)*gap/4-originalDebit r at hgap
  nlinarith only [hmul,hprice,hgap,hgain]

end QRH.Cycle092.MixedOutsidePaid
#print axioms QRH.Cycle092.MixedOutsidePaid.original_inverse_high_price_paid
