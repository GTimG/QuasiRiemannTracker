import Candidate.Target830.Physical.Geometry
import Candidate.Cycle25.Numerator.SourceSelection

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

namespace OAI.SevenEighths.Target830.Physical
open Cycle25.Numerator
open HeckeDetectorPhysicalSelection

/-- Selection on the original full slot family, with error gains zeroed.
The cardinality, labels and row polynomials are not changed. -/
theorem scheduled_whole_slots (P : SourcePlane) {Slot : Type*}
    [Fintype Slot] [DecidableEq Slot]
    (d v delta mesh : ℝ) (hd : dMinus ≤ d ∧ d ≤ dPlus)
    (hv : 0 ≤ v) (hdelta : 0 ≤ delta) (hmesh : 0 < mesh)
    (widths : Slot → ℝ) (hw : ∀ j, 0 ≤ widths j)
    (hwm : ∀ j, widths j ≤ mesh) (hsum : ∑ j, widths j = ell / d)
    (main : Finset Slot) (g : Slot → ℝ)
    (hg : ∀ j, 0 ≤ g j ∧ g j ≤ delta / 2)
    (herror : ∀ j, j ∉ main → g j = 0) :
    let a := weightedMean Finset.univ widths g
    a = (∑ j, widths j * g j) / (ell / d) ∧ 0 ≤ a ∧ a ≤ delta / 2 ∧
    ∃ selected : Finset Slot, selected ⊆ main ∧ (∀ j ∈ selected, 0 < g j) ∧
      (∑ j ∈ selected, widths j) ≤ scheduledCapacity P d v ∧
      a * scheduledCapacity P d v - (delta / 2) * mesh ≤
        ∑ j ∈ selected, widths j * g j ∧
      ∀ U : ℝ, 1 ≤ U → ∀ Q : Slot → ℂ,
        (∀ j, 0 < g j → U ^ (2 * widths j * g j) ≤ ‖Q j‖ ^ 2) →
        U ^ (2 * a * scheduledCapacity P d v - delta * mesh) ≤
          ‖∏ j ∈ selected, Q j‖ ^ 2 := by
  have hdpos := physical_d_pos hd.1
  have hell : 0 < ell := by norm_num [ell, theta]
  have hL : 0 < ∑ j, widths j := by rw [hsum]; exact div_pos hell hdpos
  have hcap : scheduledCapacity P d v ≤ ∑ j, widths j := by
    rw [hsum]
    exact scheduledCapacity_le_supply P hd hv
  obtain ⟨ha, had⟩ := weightedMean_bounds Finset.univ widths g delta
    (fun j _ => hw j) hL (fun j _ => hg j)
  obtain ⟨T, _, hT, hTpos, hTcap, hgain, hspike⟩ := SlotSelection.zero_error_whole_slots
    Finset.univ main widths g delta mesh (scheduledCapacity P d v)
    hdelta hmesh.le (fun j _ => hw j) (fun j _ => hwm j) hL
    (fun j _ => hg j) (fun j _ => herror j)
    (scheduledCapacity_nonneg P hd hv) hcap
  refine ⟨?_, ha, had, T, hT, hTpos, hTcap, hgain, ?_⟩
  · unfold weightedMean
    rw [hsum]
  · intro U hU Q hQ
    exact hspike U hU Q (fun j _ => hQ j)

end OAI.SevenEighths.Target830.Physical

#print axioms OAI.SevenEighths.Target830.Physical.scheduled_whole_slots
