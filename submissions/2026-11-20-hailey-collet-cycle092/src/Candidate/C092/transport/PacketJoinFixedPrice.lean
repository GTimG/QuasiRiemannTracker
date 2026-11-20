/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native direct certificate at the actual conductor, with explicit source/count fees. -/
import Candidate.C092.transport.PacketJoinMean
import Candidate.C092.transport.PacketJoinFixedWindow
import Candidate.C092.transport.DirectCertificates
import Candidate.C092.transport.SelectedNonfloorPrice
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open QRH.Record1252270103Return
open QRH.Cycle090 QRH.Cycle092.Direct QRH.Cycle092.DirectCount
open QRH.Cycle092.SelectedNonfloor QRH.Coverage
namespace QRH.Cycle092.PacketJoin
variable [Geometry.Parameters]


/-- Both literal fixed-count faces are checked on the same actual cell. -/
def fixedTopAdmission (δ p : ℝ) : Prop :=
  ∃ cS cA : DirectCertificate,
    cS∈directCertificates ∧ cS.route=.fixedS ∧ cS.edge=3 ∧ cS.box.Contains (δ,p) ∧
    cA∈directCertificates ∧ cA.route=.fixedA ∧ cA.edge=3 ∧ cA.box.Contains (δ,p)

lemma fixed_value_lower {δ p : ℝ} (hδ : 0≤δ) (hp : 0≤p) (hp' : p≤1/2) :
    1-δ≤PacketJoinFixed.Return.value δ p := by
  have hb := (PacketJoinFixed.Return.continuations hp hp').2.2.2.2
  have hm := mul_le_mul_of_nonneg_left hb.le hδ
  have hs : 1-δ≤PacketJoinFixed.Return.short δ p := by
    unfold PacketJoinFixed.Return.short
    nlinarith
  exact hs.trans (le_max_left _ _)

theorem fixed_row_price_le_top {δ p D : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2)
    (hD : 0<D) (hDh : D≤Geometry.h) :
    rowPrice δ p (PacketJoinFixed.Return.value δ p) D sourceCost ≤
      rowPrice δ p (PacketJoinFixed.Return.value δ p) Geometry.h sourceCost := by
  have hh : 0<Geometry.h := hD.trans_le hDh
  have hcD := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hD
  have hch := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hh
  have hcap := cappedCapacity_increment_le physicalCap_admissible.1.le allowances_pos.1.le hDh (y:=Geometry.y)
  have hr := fixed_value_lower hδ hp hp'
  have hdp : 0≤δ*p := mul_nonneg hδ hp
  have hdphi : δ*p≤3/8 := by nlinarith [mul_le_mul_of_nonneg_left hp' hδ]
  have hc : 0≤3*PacketJoinFixed.Return.value δ p/4-9/100-δ*p*physicalCap/2 := by
    norm_num [physicalCap]
    nlinarith
  have hweight := mul_le_mul_of_nonneg_left hcap hdp
  have hnonneg := mul_nonneg hc (sub_nonneg.mpr hDh)
  unfold rowPrice
  rw [hcD,hch]
  nlinarith


lemma fixed_row_price_of_certificates {δ p d : ℝ} (had : fixedTopAdmission δ p)
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper)
    (hell : Geometry.ell=Physical.ell)
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2)
    (hd : 0<d) (hdh : d≤Geometry.h) :
    rowPrice δ p (PacketJoinFixed.Return.value δ p) d sourceCost≤theta-1/2500000 := by
  obtain ⟨cS,cA,hmS,hrS,heS,hpS,hmA,hrA,heA,hpA⟩ := had
  have hs := certified_original_price hmS hh hh' hpS
  have ha := certified_original_price hmA hh hh' hpA
  rw [hrS,heS] at hs
  rw [hrA,heA] at ha
  have hgeom : 0<Geometry.h := hd.trans_le hdh
  have hy : Geometry.y=Geometry.h-2*Geometry.ell := by
    unfold Geometry.h
    linarith [Geometry.x_add_y]
  have hcap := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hgeom
  have eqPrice (route : CountRoute) (hr : route=.fixedS ∨ route=.fixedA) :
      rowPrice δ p (countN route sourceCost kap δ p) Geometry.h sourceCost =
        originalPrice route 3 Geometry.h δ p := by
    unfold rowPrice
    rw [hcap,hy,hell]
    rcases hr with rfl | rfl <;> simp [originalPrice,originalCapacity,edgeD,countJ]
  have hRle := PacketJoinFixed.Return.value_le_priced hδ hp
  unfold PacketJoinFixed.Return.pricedValue at hRle
  have htop : rowPrice δ p (PacketJoinFixed.Return.value δ p) Geometry.h sourceCost≤theta-1/2500000 := by
    by_cases h : countN .fixedS sourceCost kap δ p≤countN .fixedA sourceCost kap δ p
    · rw [max_eq_right h] at hRle
      have hm := mul_le_mul_of_nonneg_left hRle hgeom.le
      have heq := eqPrice .fixedA (Or.inr rfl)
      unfold rowPrice at heq ⊢
      linarith
    · rw [max_eq_left (le_of_not_ge h)] at hRle
      have hm := mul_le_mul_of_nonneg_left hRle hgeom.le
      have heq := eqPrice .fixedS (Or.inl rfl)
      unfold rowPrice at heq ⊢
      linarith
  exact (fixed_row_price_le_top hδ hδ' hp hp' hd hdh).trans htop

end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.fixed_row_price_of_certificates
