/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine saved count at the actual upper padded conductor. -/
import Candidate.C092.transport.PacketJoinPaddedPrice
import Candidate.C092.transport.PacketJoinOldCount
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open OAI.SevenEighths QRH.Record1252270103Return
open QRH.Cycle090 QRH.Cycle092.Direct QRH.Cycle092.DirectCount
open QRH.Cycle092.SelectedNonfloor QRH.Coverage
namespace QRH.Cycle092.PacketJoin

lemma old_kap_range : (7/10:ℝ)≤Direct.kap ∧ Direct.kap≤3/4 :=
  ⟨by norm_num [Direct.kap,QRH.ContactCertificate.alphaHi],source_contact_guards.2.2.2⟩

lemma old_value_bounds {δ p : ℝ} (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2) :
    1-δ≤Cycle25DetectorRowCount.rowCount δ p Direct.kap ∧
      Cycle25DetectorRowCount.rowCount δ p Direct.kap≤2 := by
  have hc := Cycle25DetectorRowCount.coefficient_nonneg hp hp' old_kap_range.1 old_kap_range.2
  have hv : 0<Cycle25DetectorRowCount.V δ := by unfold Cycle25DetectorRowCount.V;linarith
  have hw : 0≤δ*Cycle25DetectorRowCount.coefficient p Direct.kap := mul_nonneg hδ hc
  have hd : 0<2*(Cycle25DetectorRowCount.V δ+δ*Cycle25DetectorRowCount.coefficient p Direct.kap) := by positivity
  have h0 : 0≤δ*Cycle25DetectorRowCount.coefficient p Direct.kap*Cycle25DetectorRowCount.V δ/
      (2*(Cycle25DetectorRowCount.V δ+δ*Cycle25DetectorRowCount.coefficient p Direct.kap)) := by positivity
  have h1 : δ*Cycle25DetectorRowCount.coefficient p Direct.kap*Cycle25DetectorRowCount.V δ/
      (2*(Cycle25DetectorRowCount.V δ+δ*Cycle25DetectorRowCount.coefficient p Direct.kap))≤Cycle25DetectorRowCount.V δ/2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (Cycle25DetectorRowCount.V δ)]
  unfold Cycle25DetectorRowCount.rowCount
  constructor
  · linarith
  · unfold Cycle25DetectorRowCount.V at h1 ⊢
    linarith

variable [Geometry.Parameters]
lemma old_row_price_padded {c : DirectCertificate}
    (hc : c∈directCertificates) (hr : c.route=.old) (he : c.edge=3)
    {δ p d : ℝ} (hpbox : c.box.Contains (δ,p))
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper) (hell : Geometry.ell=Physical.ell)
    (hδ : 0≤δ) (hδ' : δ≤3/4) (hp : 0≤p) (hp' : p≤1/2)
    (hd : 0<d) (hdh : d≤Geometry.h+rowPad) :
    rowPrice δ p (Cycle25DetectorRowCount.rowCount δ p Direct.kap) d sourceCost≤theta-1/2500000+2*rowPad := by
  have hgeom : 0<Geometry.h := (by norm_num [hLower] : (0:ℝ)<hLower).trans_le hh
  have hpayed := certified_original_price hc hh hh' hpbox
  rw [hr,he] at hpayed
  have hy : Geometry.y=Geometry.h-2*Geometry.ell := by unfold Geometry.h;linarith [Geometry.x_add_y]
  have hcap := Physical.Selection.scaled_zero_capacity (y:=Geometry.y) (s:=sourceCost) hgeom
  have heq : rowPrice δ p (Cycle25DetectorRowCount.rowCount δ p Direct.kap) Geometry.h sourceCost =
      originalPrice .old 3 Geometry.h δ p := by
    rw [old_rowCount_eq δ p Direct.kap hδ hδ' hp hp' old_kap_range.1 old_kap_range.2]
    unfold rowPrice
    rw [hcap,hy,hell]
    rfl
  obtain ⟨hlo,hhi⟩ := old_value_bounds hδ hδ' hp hp'
  apply row_price_padded_of_top hδ hδ' hp hp' hlo hhi hgeom hd hdh
  rw [heq]
  linarith
end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.old_row_price_padded
