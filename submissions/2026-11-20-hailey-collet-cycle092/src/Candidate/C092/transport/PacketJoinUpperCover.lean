/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original top direct and all current-exterior regions form one actually
counted upper sector. The mixed alternative remains explicit. -/
import Candidate.C092.transport.PacketJoinUpperSector
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open QRH.Record1252270103Return
open QRH.Cycle090 QRH.Cycle092.Direct QRH.Coverage QRH.PhysicalCertificate QRH.ContactCertificate
namespace QRH.Cycle092.PacketJoin
variable [Geometry.Parameters]

lemma upper_sector_of_actual_top_direct {index : Fin 57} {leaf : DirectLeaf}
    (hm : leaf∈(initialAt index).directRecords) (he : (originalAt index).edge=3)
    {δ p : ℝ} (hp : leaf.box.Contains (δ,p)) : upperSectorAdmission δ p := by
  have hc := otherLeafCheck_sound _ _ (otherTreeCheck_sound _ _ (actual_initial_other_check index) hm)
  rcases hc with hr | ⟨hr,c,hc,hroute,hedge,hin⟩ | ⟨hr,c,hc,hroute,hedge,hin⟩ | ⟨hr,hs,ha⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl (e49_box_of_actual_leaf hm hr hp))))
  · exact Or.inl ⟨c,hc,hroute,Fin.ext (hedge.trans he),Box.contains_of_included hin hp⟩
  · exact Or.inr (Or.inl ⟨c,hc,hroute,Fin.ext (hedge.trans he),Box.contains_of_included hin hp⟩)
  · exact Or.inr (Or.inr (Or.inl (fixed_top_admission_of_actual_leaf hm hr he hp)))

lemma upper_sector_of_actual_exterior {leaf : StoredLeaf}
    (hm : leaf∈forestRecords qForest) (hr : leaf.route≠.mixed)
    {δ p : ℝ} (hp : leaf.box.Contains (δ,p)) : upperSectorAdmission δ p :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨leaf,hm,hr,hp⟩)))

/-- Every original closed point at every actual upper padded conductor is in
this genuine counted sector or the separately retained mixed sector. -/
theorem actual_upper_sector_or_mixed {x d : ℝ} {point : Point}
    (hh : hLower≤Geometry.h) (hh' : Geometry.h≤hUpper)
    (hx : QRH.RationalInterval.Contains alphaInterval x)
    (hd : (1/2:ℝ)≤d) (hdh : d≤Geometry.h+rowPad)
    (hp : originalDomain.Contains point) :
    upperSectorAdmission point.1 point.2 ∨
      ActualMixedPrice.MixedPaid Geometry.h x d point := by
  rcases ActualMixedPrice.full_original_price_cover 3 hh hh' hx
    ((by norm_num : (1/100:ℝ)≤1/2).trans hd) hdh hp with hdir|hext|hmix
  · obtain ⟨i,he,leaf,hm,hp,_⟩ := hdir
    exact Or.inl (upper_sector_of_actual_top_direct hm he hp)
  · obtain ⟨leaf,hm,hr,hp,_⟩ := hext
    exact Or.inl (upper_sector_of_actual_exterior hm hr hp)
  · exact Or.inr hmix
end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.actual_upper_sector_or_mixed
