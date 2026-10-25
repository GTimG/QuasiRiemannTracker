/- Copyright (c) 2026 Sil. Apache-2.0.
Continuous scalar return from the complete finite certificate. The same concrete
finite envelope is held fixed as the conductor varies. No analytical counting
bound, source theorem, or zero-free conclusion is a hypothesis or a conclusion. -/
import Candidate.SilPrior.FourthPower.ReturnFinite

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReturnContinuous
noncomputable section
open ReturnCertificate ReturnFinite

/-- Interpolation with the capacity identity cleared by the interval length. -/
theorem interval_return {a b d Ca Cb C δ p R B : ℝ}
    (hab : a < b) (hda : a ≤ d) (hdb : d ≤ b)
    (hC : (b-a)*C = (b-d)*Ca+(d-a)*Cb)
    (ha : returnValue a Ca δ p R ≤ B)
    (hb : returnValue b Cb δ p R ≤ B) :
    returnValue d C δ p R ≤ B := by
  let u : ℝ := (d-a)/(b-a)
  have hba : b-a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hu : u ∈ Set.Icc 0 1 :=
    Cycle61.Arithmetic.Bernstein.normalize_mem hab ⟨hda, hdb⟩
  have hd : (1-u)*a+u*b = d := by
    dsimp [u]
    field_simp [hba]
    <;> ring
  have hc : (1-u)*Ca+u*Cb = C := by
    dsimp [u]
    field_simp [hba]
    nlinarith [hC]
  have hret := interpolate_return hu.1 hu.2 ha hb
  rw [hd, hc] at hret
  exact hret

/-- The old capacity on its entire interval, including the kink at y. -/
theorem old_return {δ p d : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hd0 : d0 ≤ d) (hds : d ≤ ds) :
    returnValue d (oldCapacity kappa d) δ p (envelope δ p) ≤ theta-reserve := by
  have hstart : returnValue d0 (oldCapacity kappa d0) δ p (envelope δ p) ≤
      theta-reserve := by
    simpa only [edgeD, edgeC] using edge_return_bound .oldsmall hδ hp
  have hpeak : returnValue y (oldCapacity kappa y) δ p (envelope δ p) ≤
      theta-reserve := by
    simpa only [edgeD, edgeC] using edge_return_bound .oldpeak hδ hp
  have hjoin : returnValue ds (oldCapacity kappa ds) δ p (envelope δ p) ≤
      theta-reserve := by
    simpa only [edgeD, edgeC] using edge_return_bound .oldswitch hδ hp
  have h0y : d0 < y := conductor_order.1
  have hys : y < ds := conductor_order.2.1
  by_cases hdy : d ≤ y
  · rw [old_capacity_left hdy]
    rw [old_capacity_left h0y.le] at hstart
    rw [old_capacity_left le_rfl] at hpeak
    exact interval_return (Ca := d0/(6*kappa)) (Cb := y/(6*kappa))
      h0y hd0 hdy (by ring) hstart hpeak
  · have hyd : y ≤ d := le_of_not_ge hdy
    rw [old_capacity_right hyd]
    rw [old_capacity_right le_rfl] at hpeak
    rw [old_capacity_right hys.le] at hjoin
    exact interval_return (Ca := (2*y-y)/(6*kappa)) (Cb := (2*y-ds)/(6*kappa))
      hys hyd hds (by ring) hpeak hjoin

/-- The new physical capacity on its full interval, including its narrow final piece. -/
theorem new_return {δ p d : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hds : ds ≤ d) (hdp : d ≤ dplus) :
    returnValue d (newCapacity d) δ p (envelope δ p) ≤ theta-reserve := by
  have hjoin : returnValue ds (newCapacity ds) δ p (envelope δ p) ≤
      theta-reserve := by
    simpa only [edgeD, edgeC] using edge_return_bound .newswitch hδ hp
  have hkink : returnValue dk (newCapacity dk) δ p (envelope δ p) ≤
      theta-reserve := by
    simpa only [edgeD, edgeC] using edge_return_bound .newkink hδ hp
  have htop : returnValue dplus (newCapacity dplus) δ p (envelope δ p) ≤
      theta-reserve := by
    simpa only [edgeD, edgeC] using edge_return_bound .newtop hδ hp
  have hsk : ds < dk := conductor_order.2.2.1
  have hkp : dk < dplus := conductor_order.2.2.2.1
  by_cases hdk : d ≤ dk
  · rw [new_capacity_left hdk]
    rw [new_capacity_left hsk.le] at hjoin
    rw [new_capacity_left le_rfl] at hkink
    exact interval_return (Ca := sPhysical*ds) (Cb := sPhysical*dk)
      hsk hds hdk (by ring) hjoin hkink
  · have hkd : dk ≤ d := le_of_not_ge hdk
    rw [new_capacity_right hkd]
    rw [new_capacity_right le_rfl] at hkink
    rw [new_capacity_right hkp.le] at htop
    exact interval_return
      (Ca := (2*y-(2-physicalIntercept)*dk)/physicalSlope)
      (Cb := (2*y-(2-physicalIntercept)*dplus)/physicalSlope)
      hkp hkd hdp (by ring) hkink htop

def selectedCapacity (d : ℝ) : ℝ :=
  if d ≤ ds then oldCapacity kappa d else newCapacity d

theorem capacity_switch_agreement : oldCapacity kappa ds = newCapacity ds :=
  capacity_joins.1.trans capacity_joins.2.1.symm

/-- Complete scalar return on the entire closed conductor interval. -/
theorem complete_return {δ p d : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hd : d ∈ Set.Icc d0 dplus) :
    returnValue d (selectedCapacity d) δ p (envelope δ p) ≤ theta-reserve := by
  by_cases hds : d ≤ ds
  · rw [selectedCapacity, if_pos hds]
    exact old_return hδ hp hd.1 hds
  · rw [selectedCapacity, if_neg hds]
    exact new_return hδ hp (le_of_not_ge hds) hd.2

end
end Candidate.SilPrior.FourthPower.ReturnContinuous
