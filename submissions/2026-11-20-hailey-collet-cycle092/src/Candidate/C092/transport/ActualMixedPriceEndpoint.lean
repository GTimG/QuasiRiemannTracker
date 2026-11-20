/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.ActualMixedPricePadded
import Candidate.C092.transport.DirectAll

/-! The full original closed-domain cover, interpreted by actual route prices.
Direct certificates below retain their proved top-conductor scope; refined
exterior and mixed certificates hold on the actual padded conductor support.
This file does not identify these scalar prices with a bound on the selected
Mellin integral without the missing analytic row-packet transport. -/
set_option autoImplicit false
namespace QRH.Cycle092.ActualMixedPrice
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed
open QRH.ContactCertificate QRH.PhysicalCertificate QRH.Coverage
noncomputable section

/-- Exact original-route top price: old, native, both fixed faces, or E49. -/
def DirectPaid (edge : Fin 4) (h x : ℝ) (point : Point) : Prop :=
  ∃ index : Fin 57, (originalAt index).edge=edge.val ∧
    ∃ leaf∈(initialAt index).directRecords, leaf.box.Contains point ∧
      (1/125000000 : ℝ)≤theta-Direct.directPrice edge leaf h point.1 point.2
        (g0 (wValue x)) (g1 (wValue x))

/-- Every added exterior terminal uses its literal physical price at D. -/
def ExteriorPaid (h x D : ℝ) (point : Point) : Prop :=
  ∃ leaf∈forestRecords qForest, leaf.route≠.mixed ∧ leaf.box.Contains point ∧
    0<theta-Physical.price h point.1 point.2 (g0 (wValue x)) (g1 (wValue x)) D-
      paddingDebit-1/100000000000000

/-- Every mixed terminal pays the live Q1 physical debit at every Q2 offset
and length, with all ten real contact-conductor guards and a uniform reserve. -/
def MixedPaid (h x D : ℝ) (point : Point) : Prop :=
  ∃ r∈rows, r.box.Contains point ∧
    (∀ i : Fin 10, (1/1000 : ℝ)≤Direct.pairedGuard i point.1 point.2
      (g0 (wValue x)) (g1 (wValue x))) ∧
    ∀ ξ z : ℝ, 0≤ξ → ξ≤(rowGamma r.box r.B : ℝ) → widthLo≤z → z≤widthHi →
      (1/1000000000000 : ℝ)<saving r h point.1 point.2 x D ξ z-
        paddingDebit-1/100000000000000

/-- A uniform finite endpoint consumer with no stored-price interpretation
premise: all57 cells, allfour original edges, every closed boundary. -/
theorem full_original_price_cover (edge : Fin 4) {h x D : ℝ} {point : Point}
    (hh : hLower≤h) (hh' : h≤hUpper)
    (hx : QRH.RationalInterval.Contains alphaInterval x)
    (hD : (1/100 : ℝ)≤D) (hDh : D≤h+rowPad)
    (hp : originalDomain.Contains point) :
    DirectPaid edge h x point ∨ ExteriorPaid h x D point ∨ MixedPaid h x D point := by
  obtain ⟨index,he,hd | hc⟩ := original_domain_covered edge hp
  · obtain ⟨leaf,hm,hp,_⟩ := hd
    have hcontact := Physical.actual_contact_bounds hx
    obtain ⟨e,he',hpaid⟩ := Direct.all_actual_direct_prices hm hh hh' hp
      hcontact.1 hcontact.2.1 hcontact.2.2.1 hcontact.2.2.2
    have heq : e=edge := Fin.ext (he'.trans he)
    exact Or.inl ⟨index,he,leaf,hm,hp,heq ▸ hpaid⟩
  · obtain ⟨root,hm,_,hp⟩ := hc
    obtain ⟨leaf,hl,hp,_⟩ := forest_covers_record qForest_checked ⟨root,hm,hp⟩
    by_cases hr : leaf.route=.mixed
    · obtain ⟨r,hm,heq,_⟩ := Top.actual_mixed_row hl hr
      have hp' : r.box.Contains point := heq.symm ▸ hp
      refine Or.inr (Or.inr ⟨r,hm,hp',full_admission hm hp' hx,?_⟩)
      intro ξ z hξ hξ' hz hz'
      exact all_rows_uniform_physical_reserve hm hh hh' hp' hx hD hDh hξ hξ' hz hz'
    · exact Or.inr (Or.inl ⟨leaf,hl,hr,hp,
        Physical.all_exterior_padded_support_positive hl hr hh hh' hp hx hDh⟩)

end
end QRH.Cycle092.ActualMixedPrice
#print axioms QRH.Cycle092.ActualMixedPrice.full_original_price_cover
