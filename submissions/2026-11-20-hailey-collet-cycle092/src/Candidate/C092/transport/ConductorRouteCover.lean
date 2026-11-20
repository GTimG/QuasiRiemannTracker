/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The certified edge alternatives cover the live conductor, including switches
between different direct count routes on the two ends of an interval. -/
import Candidate.C092.transport.ConductorActual

namespace QRH.Cycle092.Direct
noncomputable section
set_option autoImplicit false
open QRH.Cycle090 QRH.Coverage QRH.PhysicalCertificate QRH.ContactCertificate
open QRH.Cycle092.ActualMixedPrice

def activeCapacity (h D : ℝ) : ℝ :=
  if D ≤ 19/25 then min D (2*yLength h-D)/(6*kap)
  else cappedCapacity physicalCap (yLength h) sourceCost D

def endpointMember (edge : Fin 4) (l : DirectLeaf) (point : Point) : Prop :=
  ∃ i : Fin 57, (originalAt i).edge=edge.val ∧ l ∈ (initialAt i).directRecords ∧ l.box.Contains point

def liveDirectPaid (h x D : ℝ) (point : Point) : Prop :=
  let lo : Fin 4 := if D ≤ 19/25 then 0 else 2
  let hi : Fin 4 := if D ≤ 19/25 then 1 else 3
  ∃ l r : DirectLeaf, endpointMember lo l point ∧ endpointMember hi r point ∧
    ∀ R : ℝ, R ≤ leafCount l point.1 point.2 (g0 (wValue x)) (g1 (wValue x)) →
      R ≤ leafCount r point.1 point.2 (g0 (wValue x)) (g1 (wValue x)) →
      conductorPrice (priceBase h point.1 point.2) point.1 point.2 R (activeCapacity h D) D ≤ theta-1/125000000

/-- Every admissible point and every unpadded conductor. For two direct
certificates the scalar price holds at any count paid by both endpoints. -/
theorem live_conductor_cover {h x D : ℝ} {point : Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hx : QRH.RationalInterval.Contains alphaInterval x)
    (hD : 1/100 ≤ D) (hDh : D ≤ h) (hp : originalDomain.Contains point) :
    liveDirectPaid h x D point ∨ ExteriorPaid h x D point ∨ MixedPaid h x D point := by
  have hedge (k : Fin 4) := full_original_price_cover k hh hh' hx hD
    (hDh.trans (by have := (show (0:ℝ) ≤ rowPad by unfold rowPad; positivity); linarith)) hp
  have hpos : 0 ≤ point.1*point.2 := mul_nonneg (by simpa [originalDomain] using hp.1) (by simpa [originalDomain] using hp.2.2.1)
  by_cases hside : D ≤ 19/25
  · rcases hedge 0 with ha|ha
    · rcases hedge 1 with hb|hb
      · obtain ⟨i,hi,l,hl,hpl,hleft⟩ := direct_paid_count hh ha
        obtain ⟨j,hj,r,hr,hpr,hright⟩ := direct_paid_count hh hb
        left
        refine ⟨l,r,?_,?_,?_⟩
        · simpa [hside,endpointMember] using (show endpointMember 0 l point from ⟨i,hi,hl,hpl⟩)
        · simpa [hside,endpointMember] using (show endpointMember 1 r point from ⟨j,hj,hr,hpr⟩)
        · intro R hR hR'
          rw [activeCapacity,if_pos hside]
          exact natural_chord _ _ _ ((by norm_num : (1/200:ℝ)≤1/100).trans hD) hside hpos hR hR' hleft hright
      · exact Or.inr hb
    · exact Or.inr ha
  · rcases hedge 2 with ha|ha
    · rcases hedge 3 with hb|hb
      · obtain ⟨i,hi,l,hl,hpl,hleft⟩ := direct_paid_count hh ha
        obtain ⟨j,hj,r,hr,hpr,hright⟩ := direct_paid_count hh hb
        left
        refine ⟨l,r,?_,?_,?_⟩
        · simpa [hside,endpointMember] using (show endpointMember 2 l point from ⟨i,hi,hl,hpl⟩)
        · simpa [hside,endpointMember] using (show endpointMember 3 r point from ⟨j,hj,hr,hpr⟩)
        · intro R hR hR'
          rw [activeCapacity,if_neg hside]
          exact native_chord _ _ _ hh (le_of_not_ge hside) hDh hpos hR hR' hleft hright
      · exact Or.inr hb
    · exact Or.inr ha

#print axioms live_conductor_cover
end
end QRH.Cycle092.Direct
