/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual conductor padding for genuine native, fixed and E49 counted packets. -/
import Candidate.C092.transport.PacketJoinFixedAdmission
import Candidate.C092.transport.PacketJoinFinalFee
import Candidate.C092.transport.ConductorPadded
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open QRH.Record1252270103Return
open QRH.Cycle090 QRH.Cycle092.Direct QRH.Cycle092.DirectCount
open QRH.Cycle092.SelectedNonfloor QRH.Coverage
namespace QRH.Cycle092.PacketJoin
variable [Geometry.Parameters]

lemma native_value_upper {δ p : ℝ} (hδ : 0≤δ) (hp : 0≤p) (hp' : p≤1/2)
    (hg : ∀ j:Fin 15,0<nativeGuard j sourceCost δ p) : nativeValue sourceCost δ p≤2 := by
  have hn := native_data hδ hp hg
  have hc := native_cross_identity sourceCost δ p hn.Dpos hn.Jpos
  have hx : 0≤nativeCross sourceCost δ p := by linarith [hn.crossLo]
  have hm := mul_nonneg hδ (add_nonneg hp (mul_nonneg (by linarith : 0≤1-p) hx))
  linarith

lemma e49_value_upper {δ p : ℝ} (hav : PacketJoinE49.Return.window.Available δ p) :
    PacketJoinE49.Return.valueI δ p≤2 := by
  have hc := PacketJoinE49.Return.window.inverse_crossing hav.1 hav.2
  have hx := PacketJoinE49.Return.window.crossing_left hav.1 hav.2
  have hk := PacketJoinE49.Return.window.slope_nonneg hav.1 hav.2
  have hg := Qrh.TwoSlot.AnchorContinuum.Contact.tangent_coefficient_bounds
  have hd := hav.1.1
  have hp := hav.2.1
  change (45/128:ℝ)≤δ at hd
  change 0≤1-p*(1+2*PacketJoinE49.Return.line.g1) at hk
  have hx0 : 0≤PacketJoinE49.Return.crossingI δ p := by
    change PacketJoinE49.anchorLeft≤PacketJoinE49.Return.crossingI δ p at hx
    norm_num [PacketJoinE49.anchorLeft] at hx
    linarith
  have hg0 : 0≤PacketJoinE49.Return.line.g0 := by
    have h := hg.1
    change (5805911/100000000:ℝ)<PacketJoinE49.Return.line.g0 at h
    linarith
  have hp0 : 0≤p := by change (7/16:ℝ)≤p at hp;linarith
  have hm0 := mul_nonneg hp0 (show 0≤1+2*PacketJoinE49.Return.line.g0 by linarith)
  have hm1 := mul_nonneg hk hx0
  have hm := mul_nonneg (show 0≤δ by linarith) (add_nonneg hm0 hm1)
  change 1-δ*(p*(1+2*PacketJoinE49.Return.line.g0)+
    (1-p*(1+2*PacketJoinE49.Return.line.g1))*PacketJoinE49.Return.crossingI δ p)=PacketJoinE49.Return.valueI δ p at hc
  linarith

lemma fixed_value_upper {δ p : ℝ} (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2) :
    PacketJoinFixed.Return.value δ p≤2 := by
  have hav := PacketJoinFixed.Return.window_available hδ hδ' hp hp'
  have hk := PacketJoinFixed.Return.window.slope_nonneg hav.1 hav.2
  have hg := Qrh.TwoSlot.AnchorContinuum.Contact.tangent_coefficient_bounds
  have hg0 : 0≤PacketJoinFixed.Return.line.g0 := by
    have h := hg.1
    change (5805911/100000000:ℝ)<PacketJoinFixed.Return.line.g0 at h
    linarith
  have hb : 0≤PacketJoinFixed.Return.bracket p := by
    unfold PacketJoinFixed.Return.bracket
    exact add_nonneg (mul_nonneg hp (by linarith)) (mul_nonneg hk (by norm_num [PacketJoinFixed.Return.fixedR]))
  have hs : PacketJoinFixed.Return.short δ p≤2 := by
    unfold PacketJoinFixed.Return.short
    linarith [mul_nonneg hδ hb]
  have hl : PacketJoinFixed.Return.long δ≤2 := by
    norm_num [PacketJoinFixed.Return.long,PacketJoinFixed.Return.cutoff,PacketJoinFixed.Return.fixedR]
    linarith
  exact max_le hs hl

lemma row_price_le_top {δ p R D : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2)
    (hR : 1-δ≤R) (hD : 0<D) (hDh : D≤Geometry.h) :
    rowPrice δ p R D sourceCost≤rowPrice δ p R Geometry.h sourceCost := by
  have hh : 0<Geometry.h := hD.trans_le hDh
  have hcD := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hD
  have hch := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hh
  have hcap := cappedCapacity_increment_le physicalCap_admissible.1.le allowances_pos.1.le hDh (y:=Geometry.y)
  have hdp : 0≤δ*p := mul_nonneg hδ hp
  have hdphi : δ*p≤3/8 := by nlinarith [mul_le_mul_of_nonneg_left hp' hδ]
  have hc : 0≤3*R/4-9/100-δ*p*physicalCap/2 := by
    norm_num [physicalCap]
    nlinarith
  have hweight := mul_le_mul_of_nonneg_left hcap hdp
  have hnonneg := mul_nonneg hc (sub_nonneg.mpr hDh)
  unfold rowPrice
  rw [hcD,hch]
  nlinarith

lemma row_price_padding {δ p R d D : ℝ} (hd : 0<d) (hdD : d≤D)
    (hδ : 0≤δ*p) (hδ' : δ*p≤1) (hR : R≤2) :
    rowPrice δ p R D sourceCost≤rowPrice δ p R d sourceCost+2*(D-d) := by
  have hD : 0<D := hd.trans_le hdD
  have hcapd := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hd
  have hcapD := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hD
  have h := upper_padding_cost (base:=1/2+13*Geometry.h/75-Geometry.y/2-Geometry.ell/2+
    δ/2+δ*p*Geometry.ell) (R:=R) Geometry.y hδ hδ' hR hdD
  unfold rowPrice
  rw [hcapd,hcapD]
  unfold conductorPrice at h
  nlinarith only [h]

lemma row_price_padded_of_top {δ p R d margin : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2)
    (hRlo : 1-δ≤R) (hRhi : R≤2) (hh : 0<Geometry.h)
    (hd : 0<d) (hdh : d≤Geometry.h+rowPad)
    (htop : rowPrice δ p R Geometry.h sourceCost≤theta-margin) :
    rowPrice δ p R d sourceCost≤theta-margin+2*rowPad := by
  by_cases h : d≤Geometry.h
  · exact ((row_price_le_top hδ hδ' hp hp' hRlo hd h).trans htop).trans
      (le_add_of_nonneg_right (mul_nonneg (by norm_num) allowances_pos.2.1.le))
  · have hpad := row_price_padding hh (le_of_not_ge h) (mul_nonneg hδ hp)
      (by nlinarith [mul_le_mul hδ' hp' hp (by norm_num : (0:ℝ)≤3/4)]) hRhi
    linarith

lemma native_row_price_padded {c : DirectCertificate}
    (hc : c∈directCertificates) (hr : c.route=.native) (he : c.edge=3)
    {δ p d : ℝ} (hpbox : c.box.Contains (δ,p))
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper) (hell : Geometry.ell=Physical.ell)
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2)
    (hg : ∀ j:Fin 15,0<nativeGuard j sourceCost δ p)
    (hd : 0<d) (hdh : d≤Geometry.h+rowPad) :
    rowPrice δ p (nativeValue sourceCost δ p) d sourceCost≤theta-1/2500000+2*rowPad := by
  have hgeom : 0<Geometry.h := (by norm_num [hLower] : (0:ℝ)<hLower).trans_le hh
  exact row_price_padded_of_top hδ hδ' hp hp' (native_value_lower hδ hp hp' hg)
    (native_value_upper hδ hp hp' hg) hgeom hd hdh
    (native_row_price_of_certificate hc hr he hpbox hh hh' hell hδ hδ' hp hp' hg hgeom le_rfl)

lemma fixed_row_price_padded {δ p d : ℝ} (had : fixedTopAdmission δ p)
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper) (hell : Geometry.ell=Physical.ell)
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2)
    (hd : 0<d) (hdh : d≤Geometry.h+rowPad) :
    rowPrice δ p (PacketJoinFixed.Return.value δ p) d sourceCost≤theta-1/2500000+2*rowPad := by
  have hgeom : 0<Geometry.h := (by norm_num [hLower] : (0:ℝ)<hLower).trans_le hh
  exact row_price_padded_of_top hδ hδ' hp hp' (fixed_value_lower hδ hp hp')
    (fixed_value_upper hδ hδ' hp hp') hgeom hd hdh
    (fixed_row_price_of_certificates had hh hh' hell hδ hδ' hp hp' hgeom le_rfl)

lemma e49_row_price_padded {box : Box} (hm : box∈pairedBoxes)
    {δ p d : ℝ} (hpbox : box.Contains (δ,p))
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper) (hell : Geometry.ell=Physical.ell)
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2)
    (hd : 0<d) (hdh : d≤Geometry.h+rowPad) :
    rowPrice δ p (PacketJoinE49.Return.valueI δ p) d sourceCost≤theta-1/125000000+2*rowPad := by
  have hgeom : 0<Geometry.h := (by norm_num [hLower] : (0:ℝ)<hLower).trans_le hh
  have hav := e49_box_available hm hpbox
  exact row_price_padded_of_top hδ hδ' hp hp' (e49_value_lower hav)
    (e49_value_upper hav) hgeom hd hdh
    (e49_row_price_of_box hm hpbox hh hh' hell hδ hδ' hp hp' hgeom le_rfl)
end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.native_row_price_padded
#print axioms QRH.Cycle092.PacketJoin.fixed_row_price_padded
#print axioms QRH.Cycle092.PacketJoin.e49_row_price_padded
