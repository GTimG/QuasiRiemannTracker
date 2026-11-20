/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The fixed detector keeps its two count faces until BOTH actual lower-sector
public certificates have paid their maximum. -/
import Candidate.C092.transport.NaturalPacketLowProjection
import Candidate.C092.transport.PacketJoinFixedWindow
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open QRH.Record1252270103Return QRH.Cycle090 QRH.Cycle092.Direct QRH.Coverage
namespace QRH.Cycle092.NaturalPacketLow
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

def fixedValue (δ p : ℝ) : ℝ := max (directCount .fixedS δ p) (directCount .fixedA δ p)

lemma fixed_value_lower {δ p : ℝ} (hδ : 0≤δ) (hδ' : δ≤3/4) : 1-δ≤fixedValue δ p := by
  have ha : 1-δ≤directCount .fixedA δ p := by
    norm_num [directCount,countN,countJ]
    linarith
  exact ha.trans (le_max_right _ _)

lemma natural_price_at_lower_top (route : CountRoute) (δ p : ℝ)
    (hell : Geometry.ell=Physical.ell) :
    naturalRowPrice δ p (directCount route δ p) (19/25) = originalPrice route 1 Geometry.h δ p := by
  have hy : Geometry.y=Geometry.h-2*Geometry.ell := by unfold Geometry.h;linarith [Geometry.x_add_y]
  unfold naturalRowPrice absoluteCapacity originalPrice originalCapacity directCount
  simp only [show (1:Fin 4).val=1 from rfl,show (1:ℕ)<2 by omega,↓reduceIte,edgeD]
  rw [hy,hell]

/-- Both authentic lower-sector fixed faces pay the actual maximum count.
The lower natural source retains its full original capacity. -/
theorem natural_fixed_price_of_certificates {cS cA : DirectCertificate}
    (hS : cS∈directCertificates) (hA : cA∈directCertificates)
    (hrS : cS.route=.fixedS) (hrA : cA.route=.fixedA) (heS : cS.edge=1) (heA : cA.edge=1)
    {δ p d : ℝ} (hbS : cS.box.Contains (δ,p)) (hbA : cA.box.Contains (δ,p))
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper) (hell : Geometry.ell=Physical.ell)
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2) (hd : d≤19/25) :
    naturalRowPrice δ p (fixedValue δ p) d≤theta-1/2500000 := by
  have hs := certified_original_price hS hh hh' hbS
  have ha := certified_original_price hA hh hh' hbA
  rw [hrS,heS] at hs
  rw [hrA,heA] at ha
  have hm : Monotone (fun R : ℝ=>naturalRowPrice δ p R (19/25)) := by
    intro a b hab
    unfold naturalRowPrice
    linarith
  have htop : naturalRowPrice δ p (fixedValue δ p) (19/25)≤theta-1/2500000 := by
    unfold fixedValue
    rw [hm.map_max,natural_price_at_lower_top .fixedS δ p hell,natural_price_at_lower_top .fixedA δ p hell]
    exact max_le (by linarith) (by linarith)
  exact (natural_price_mono hδ hδ' hp hp' (fixed_value_lower hδ hδ') hd).trans htop

lemma fixed_source_value_le {δ p : ℝ} (hδ : 0≤δ) (hp : 0≤p) :
    PacketJoinFixed.Return.value δ p≤fixedValue δ p := by
  have hb := PacketJoinFixed.Return.value_le_priced hδ hp
  simpa only [PacketJoinFixed.Return.pricedValue,fixedValue,directCount,countJ,div_one] using hb

lemma natural_fixed_source_price_of_certificates {cS cA : DirectCertificate}
    (hS : cS∈directCertificates) (hA : cA∈directCertificates)
    (hrS : cS.route=.fixedS) (hrA : cA.route=.fixedA) (heS : cS.edge=1) (heA : cA.edge=1)
    {δ p d : ℝ} (hbS : cS.box.Contains (δ,p)) (hbA : cA.box.Contains (δ,p))
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper) (hell : Geometry.ell=Physical.ell)
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2) (hd : 0≤d) (hd' : d≤19/25) :
    naturalRowPrice δ p (PacketJoinFixed.Return.value δ p) d≤theta-1/2500000 := by
  have hm := mul_le_mul_of_nonneg_left (fixed_source_value_le hδ hp) hd
  have hb := natural_fixed_price_of_certificates hS hA hrS hrA heS heA hbS hbA hh hh' hell hδ hδ' hp hp' hd'
  unfold naturalRowPrice at *
  linarith

end QRH.Cycle092.NaturalPacketLow
#print axioms QRH.Cycle092.NaturalPacketLow.natural_fixed_source_price_of_certificates
