/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Whole-slot capacity and damping for the variable physical source face.
Adapted from PR137 physical Geometry (Sil and predecessor authors, Apache-2.0).
The exact factor two in the conductor-dilation shift is retained. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveOriginal
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.Geometry

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport.Selection
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103Return
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open OAI.SevenEighths
variable [Geometry.Parameters]

def plainScale (d t : ℝ) : ℝ := 1-Geometry.y/d+t
def affineCapacity (s d t : ℝ) : ℝ := (1-s-2*plainScale d t)/(2+10*s)
def clippedCapacity (s d t : ℝ) : ℝ := min (3/40) (affineCapacity s d t)
def scheduledCapacity (s d v : ℝ) : ℝ := max 0 (clippedCapacity s d (v/2))
def zeroCapacity (s d : ℝ) : ℝ := clippedCapacity s d 0

/-- A nonempty whole-slot selection is inside the actual variable source face.
No minimum positive slot width is used. -/
theorem selected_admissible_or_empty {α : Type*} (T : Finset α) (width : T → ℝ)
    {s d t : ℝ} (hs : 0 ≤ s) (hw : ∀ i, 0 < width i)
    (hselected : (∑ i, width i) ≤ scheduledCapacity s d (2*t)) :
    (2*plainScale d t+(2+10*s)*(∑ i, width i) ≤ 1-s ∧ (∑ i, width i) ≤ 3/40) ∨ T = ∅ := by
  by_cases hT : T = ∅
  · exact Or.inr hT
  · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    have hne : (Finset.univ : Finset T).Nonempty := ⟨⟨i,hi⟩,Finset.mem_univ _⟩
    have hpos : 0 < ∑ i, width i := Finset.sum_pos (fun i _ => hw i) hne
    have hsel : (∑ i, width i) ≤ max 0 (clippedCapacity s d t) := by
      simpa only [scheduledCapacity,show 2*t/2 = t by ring] using hselected
    have hc : 0 ≤ clippedCapacity s d t := by
      by_contra hn
      rw [max_eq_left (le_of_not_ge hn)] at hsel
      linarith
    rw [max_eq_right hc] at hsel
    have hcap := hsel.trans (min_le_left (3/40:ℝ) (affineCapacity s d t))
    have ha := hsel.trans (min_le_right (3/40:ℝ) (affineCapacity s d t))
    have hden : 0 < 2+10*s := by positivity
    have hm := (le_div_iff₀ hden).mp ha
    exact Or.inl ⟨by linarith,hcap⟩

theorem zeroCapacity_eq_kernel (s d : ℝ) :
    zeroCapacity s d = ClippedCapacityDamping.baseCapacity (2+10*s) (3/40) s (2*Geometry.y/d-1) := by
  unfold zeroCapacity clippedCapacity affineCapacity plainScale ClippedCapacityDamping.baseCapacity
  congr 1
  ring

theorem clippedCapacity_eq_kernel (s d t : ℝ) :
    clippedCapacity s d t =
      ClippedCapacityDamping.shiftedCapacity (2+10*s) (3/40) s (2*Geometry.y/d-1) t := by
  unfold clippedCapacity affineCapacity plainScale ClippedCapacityDamping.shiftedCapacity
  congr 1
  ring

/-- The complete shift debit is paid at every dilation, with the same strictly
positive damping used in the physical bins. -/
theorem capacity_damping {s d v a delta : ℝ} (hs : 0 ≤ s) (hv : 0 ≤ v)
    (ha : 0 ≤ a) (had : a ≤ delta/2) (hdelta : 0 ≤ delta) :
    a*zeroCapacity s d/2+(1/1000)*delta*v ≤
      delta*v/4+a*scheduledCapacity s d v/2 := by
  have hr := ClippedCapacityDamping.small_shift_reserve (2+10*s) (3/40) s
    (2*Geometry.y/d-1) (v/2) (by linarith) (by linarith)
  have hh := ClippedCapacityDamping.amplitude_of_reserve _ _ (v/2) a delta
    (by linarith) ha had hdelta hr
  rw [←zeroCapacity_eq_kernel s d,←clippedCapacity_eq_kernel s d (v/2)] at hh
  have hm := mul_le_mul_of_nonneg_left
    (le_max_right (0:ℝ) (clippedCapacity s d (v/2))) ha
  change a*clippedCapacity s d (v/2) ≤ a*scheduledCapacity s d v at hm
  have he : delta*(2*(v/2)) = delta*v := by ring
  rw [he] at hh
  linarith

/-- Total selected capacity in the physical return's original Z units. -/
theorem scaled_zero_capacity {s d : ℝ} (hd : 0 < d) :
    d*zeroCapacity s d = min ((3/40)*d) ((2*Geometry.y-(1+s)*d)/(2+10*s)) := by
  unfold zeroCapacity clippedCapacity
  rw [mul_min_of_nonneg _ _ hd.le]
  congr 1
  · ring
  · unfold affineCapacity plainScale
    field_simp
    ring

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport.Selection
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.Selection.selected_admissible_or_empty
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.Selection.capacity_damping
