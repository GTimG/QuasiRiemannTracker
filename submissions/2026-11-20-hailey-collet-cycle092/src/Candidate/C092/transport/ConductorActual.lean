/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
From actual direct leaves at the ends of a conductor interval to every point
in it, retaining both count faces of a fixed-detector leaf. -/
import Candidate.C092.transport.ConductorChord
import Candidate.C092.transport.ActualMixedPriceAll

namespace QRH.Cycle092.Direct
noncomputable section
set_option autoImplicit false
open QRH.Cycle090 QRH.Coverage QRH.PhysicalCertificate QRH.ContactCertificate
open QRH.Cycle092.ActualMixedPrice

def priceBase (h d p : ℝ) : ℝ :=
  1/2+13*h/75-(h-2*Physical.ell)/2-Physical.ell/2+d/2+d*p*Physical.ell

def directCount (r : CountRoute) (d p : ℝ) : ℝ := countN r sourceCost kap d p/countJ r sourceCost kap d p

def leafCount (leaf : DirectLeaf) (d p g₀ g₁ : ℝ) : ℝ :=
  if leaf.route = "original_saved" then directCount .old d p else
  if leaf.route = "native_current_exact" then directCount .native d p else
  if leaf.route = "fixed_interior_detector" then max (directCount .fixedS d p) (directCount .fixedA d p)
  else pairedCount d p g₀ g₁

theorem original_edge_price (r : CountRoute) (k : Fin 4) (h d p : ℝ) :
    conductorPrice (priceBase h d p) d p (directCount r d p) (originalCapacity k h) (edgeD k h)
      = originalPrice r k h d p := by unfold conductorPrice priceBase directCount originalPrice; ring

theorem leaf_edge_price {k : Fin 4} {index : Fin 57} {leaf : DirectLeaf}
    (he : (originalAt index).edge=k.val) (hm : leaf ∈ (initialAt index).directRecords)
    (h d p g₀ g₁ : ℝ) (hh : hLower ≤ h) :
    conductorPrice (priceBase h d p) d p (leafCount leaf d p g₀ g₁) (originalCapacity k h) (edgeD k h)
      = directPrice k leaf h d p g₀ g₁ := by
  by_cases h₁ : leaf.route="original_saved"
  · simpa only [leafCount,directPrice,if_pos h₁] using original_edge_price .old k h d p
  by_cases h₂ : leaf.route="native_current_exact"
  · simpa only [leafCount,directPrice,if_neg h₁,if_pos h₂] using original_edge_price .native k h d p
  by_cases h₃ : leaf.route="fixed_interior_detector"
  · simp only [leafCount,directPrice,if_neg h₁,if_neg h₂,if_pos h₃]
    rw [←original_edge_price .fixedS,←original_edge_price .fixedA]
    have hD : 0 ≤ edgeD k h := by fin_cases k <;> simp [edgeD] <;> linarith [show (0:ℝ) ≤ hLower by norm_num [hLower]]
    have hmono : Monotone (fun R => conductorPrice (priceBase h d p) d p R (originalCapacity k h) (edgeD k h)) := by
      intro a b hab
      unfold conductorPrice
      linarith only [mul_le_mul_of_nonneg_left hab hD]
    exact hmono.map_max
  · have hr : leaf.route="E49_top" := by
      rcases otherLeafCheck_sound _ _ (otherTreeCheck_sound _ _ (actual_initial_other_check index) hm) with a|a|a|a
      · exact a
      · exact False.elim (h₁ a.1)
      · exact False.elim (h₂ a.1)
      · exact False.elim (h₃ a.1)
    obtain ⟨hk,_,_,_⟩ := pairedTreeCheck_sound _ _ (actual_initial_paired_check index) hm hr
    have hk' : k=3 := Fin.ext (he.symm.trans hk)
    subst k
    simp only [leafCount,directPrice,if_neg h₁,if_neg h₂,if_neg h₃,Physical.price_eq_conductorPrice]
    rfl

/-- An endpoint supplies a genuine applicable count and its actual price.
Membership carries the admission tests needed when invoking each count. -/
theorem direct_paid_count {k : Fin 4} {h x : ℝ} {point : Point}
    (hh : hLower ≤ h) (hp : DirectPaid k h x point) :
    ∃ index : Fin 57, (originalAt index).edge=k.val ∧
      ∃ leaf ∈ (initialAt index).directRecords, leaf.box.Contains point ∧
        conductorPrice (priceBase h point.1 point.2) point.1 point.2
          (leafCount leaf point.1 point.2 (g0 (wValue x)) (g1 (wValue x)))
          (originalCapacity k h) (edgeD k h) ≤ theta-1/125000000 := by
  obtain ⟨i,he,l,hl,hm,hs⟩ := hp
  exact ⟨i,he,l,hl,hm,by rw [leaf_edge_price he hl _ _ _ _ _ hh]; linarith⟩

#print axioms direct_paid_count
end
end QRH.Cycle092.Direct
