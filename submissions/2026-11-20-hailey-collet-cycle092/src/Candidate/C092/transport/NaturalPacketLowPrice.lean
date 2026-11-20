/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine natural conductor price and the checked original old-count slice. -/
import Candidate.C092.transport.NaturalPacketLowActual
import Candidate.C092.transport.DirectCertificates
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle090 QRH.Cycle092.Direct QRH.Coverage
open QRH.Cycle092.SelectedNonfloor QRH.Cycle092.PacketJoin
open OAI OAI.SevenEighths
namespace QRH.Cycle092.NaturalPacketLow
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

def naturalRowPrice (δ p R d : ℝ) : ℝ :=
  1/2+13*Geometry.h/75-Geometry.y/2-Geometry.ell/2-9*d/100+δ/2+
    δ*p*(Geometry.ell-absoluteCapacity kap d/2)+3*d*R/4

lemma old_count_lower {δ p : ℝ} (hδ : 0≤δ) (hδ' : δ≤3/4)
    (hp : 0≤p) (hp' : p≤1/2) : 1-δ≤directCount .old δ p := by
  rw [directCount,←PacketJoin.old_rowCount_eq δ p kap hδ hδ' hp hp' q_kappa_bounds.1 q_kappa_bounds.2]
  have hc := Cycle25DetectorRowCount.coefficient_nonneg hp hp' q_kappa_bounds.1 q_kappa_bounds.2
  have hv : 0 < Cycle25DetectorRowCount.V δ := by unfold Cycle25DetectorRowCount.V;linarith
  unfold Cycle25DetectorRowCount.rowCount
  exact le_add_of_nonneg_right (by positivity)

lemma natural_capacity_increment {d d' : ℝ} (hdd : d≤d') :
    absoluteCapacity kap d'-absoluteCapacity kap d≤(d'-d)/4 := by
  have hk : 0 < 6*kap := by have h:=q_kappa_bounds.1;linarith
  have hmin : min d' (2*Geometry.y-d')-min d (2*Geometry.y-d) ≤ d'-d := by
    by_cases hh : d≤2*Geometry.y-d
    · rw [min_eq_left hh]
      linarith [min_le_left d' (2*Geometry.y-d')]
    · rw [min_eq_right (le_of_not_ge hh)]
      linarith [min_le_right d' (2*Geometry.y-d')]
  have hi : absoluteCapacity kap d'-absoluteCapacity kap d =
      (min d' (2*Geometry.y-d')-min d (2*Geometry.y-d))/(6*kap) := by unfold absoluteCapacity;ring
  rw [hi]
  apply (div_le_div_of_nonneg_right hmin hk.le).trans
  apply (div_le_iff₀ hk).2
  have hΔ : 0≤d'-d := sub_nonneg.mpr hdd
  have hκ := q_kappa_bounds.1
  nlinarith [mul_nonneg hΔ (show 0≤6*kap-4 by linarith)]

/-- With the authentic old count, increasing the natural conductor only
increases its price. Both arms of the actual minimum capacity are retained. -/
lemma natural_old_price_mono {δ p d d' : ℝ} (hδ : 0≤δ) (hδ' : δ≤3/4)
    (hp : 0≤p) (hp' : p≤1/2) (hdd : d≤d') :
    naturalRowPrice δ p (directCount .old δ p) d ≤
      naturalRowPrice δ p (directCount .old δ p) d' := by
  have hcap := natural_capacity_increment hdd
  have hr := old_count_lower hδ hδ' hp hp'
  have hprod : 0≤δ*p := mul_nonneg hδ hp
  have hprod' : δ*p≤3/8 := by nlinarith [mul_le_mul_of_nonneg_left hp' hδ]
  have hcoef : 0≤3*(directCount .old δ p)/4-9/100-δ*p/8 := by nlinarith
  have hw := mul_le_mul_of_nonneg_left hcap hprod
  have hn := mul_nonneg hcoef (sub_nonneg.mpr hdd)
  unfold naturalRowPrice
  nlinarith

/-- The original old-count certificate at d=.76 pays the whole lower natural
conductor interval. No assumption about a different endpoint leaf is made. -/
theorem natural_old_price_of_certificate {c : DirectCertificate}
    (hc : c∈directCertificates) (hr : c.route=.old) (he : c.edge=1)
    {δ p d : ℝ} (hpbox : c.box.Contains (δ,p))
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper)
    (hell : Geometry.ell=Physical.ell)
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2) (hd : d≤19/25) :
    naturalRowPrice δ p (directCount .old δ p) d ≤ theta-1/2500000 := by
  have hb := certified_original_price hc hh hh' hpbox
  rw [hr,he] at hb
  have hy : Geometry.y=Geometry.h-2*Geometry.ell := by unfold Geometry.h;linarith [Geometry.x_add_y]
  have heq : naturalRowPrice δ p (directCount .old δ p) (19/25) =
      originalPrice .old 1 Geometry.h δ p := by
    unfold naturalRowPrice absoluteCapacity originalPrice originalCapacity directCount
    simp only [show (1:Fin 4).val=1 from rfl,show (1:ℕ)<2 by omega,↓reduceIte,edgeD]
    rw [hy,hell]
  have hm := natural_old_price_mono hδ hδ' hp hp' hd
  rw [heq] at hm
  linarith

lemma natural_power_le_final_iff (a p R d moment mass fee target : ℝ) (hd : 0<d) :
    naturalPacketPower a p R d moment mass ≤ finalPower a d sourceCost fee target ↔
    naturalRowPrice (2*a-1) p R d+d*(moment/4+mass)+fee≤target := by
  have hc := base_scaled (κ:=kap) hd
  have heq : baseCapacity kap d=absoluteCapacity kap d/d :=
    (eq_div_iff hd.ne').2 (by simpa only [mul_comm] using hc)
  have h : (naturalPacketPower a p R d moment mass-1/4)*d =
      naturalRowPrice (2*a-1) p R d-rowPrice (2*a-1) 0 0 d sourceCost+d*(moment/4+mass) := by
    unfold naturalPacketPower naturalRowPrice rowPrice
    rw [heq]
    field_simp
    <;> ring
  unfold finalPower
  rw [←sub_le_iff_le_add',le_div_iff₀ hd,h]
  constructor <;> intro hs <;> linarith only [hs]

lemma natural_price_with_losses (D : BaselineData) (P : TransportParameters D)
    {c : DirectCertificate} (hc : c∈directCertificates) (hr : c.route=.old) (he : c.edge=1)
    {a d p fee : ℝ} (hpbox : c.box.Contains (2*a-1,p))
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper)
    (hell : Geometry.ell=Physical.ell) (ha : 51/100<a) (ha' : a≤7/8)
    (hp : 0≤p) (hp' : p≤1/2) (hd : d≤19/25)
    (hbudget : d*(3*(159*D.ε+8*D.t+P.mesh)/4+(2*D.t)/4+nativeMass D a d)+fee≤1/5000000) :
    naturalRowPrice (2*a-1) p (naturalR D P (2*a-1) p) d+
      d*((2*D.t)/4+nativeMass D a d)+fee≤theta-1/5000000 := by
  have hb := natural_old_price_of_certificate hc hr he hpbox hh hh' hell
    (by linarith) (by linarith) hp hp' hd
  have heq : naturalRowPrice (2*a-1) p (naturalR D P (2*a-1) p) d =
      naturalRowPrice (2*a-1) p (directCount .old (2*a-1) p) d+
        3*d*(159*D.ε+8*D.t+P.mesh)/4 := by unfold naturalRowPrice naturalR;ring
  linarith

end QRH.Cycle092.NaturalPacketLow
#print axioms QRH.Cycle092.NaturalPacketLow.natural_old_price_of_certificate
#print axioms QRH.Cycle092.NaturalPacketLow.natural_power_le_final_iff
