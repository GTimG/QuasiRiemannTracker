/- Repeated marks: fork of Collet's generic return module PhysicalDirect.Selection (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Adapted from Gao Target830 physical closure, inherited OpenAI/Hailey Collet/Akash Levy; Apache-2.0. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.Schedule
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.PhysicalDirect.Geometry
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.SourceSelection
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open scoped Classical BigOperators

open QRH.Record1252270103Return

namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Geometry.BoundsR] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.RepeatedMarks.Return.GenericArithmetic OAI OAI.SevenEighths
open Cycle25.Numerator
open HeckeDetectorPhysicalSelection

/-- Selection on the original full slot family, with error gains zeroed.
The cardinality, labels and row polynomials are not changed. -/
theorem scheduled_whole_slots {Slot : Type*}
    [Fintype Slot] [DecidableEq Slot]
    (d v delta mesh : ℝ) (hd : dm ≤ d ∧ d ≤ dp)
    (hv : 0 ≤ v) (hdelta : 0 ≤ delta) (hmesh : 0 < mesh)
    (widths : Slot → ℝ) (hw : ∀ j, 0 ≤ widths j)
    (hwm : ∀ j, widths j ≤ mesh) (hsum : ∑ j, widths j = ell / d)
    (main : Finset Slot) (g : Slot → ℝ)
    (hg : ∀ j, 0 ≤ g j ∧ g j ≤ delta / 2)
    (herror : ∀ j, j ∉ main → g j = 0) :
    let a := weightedMean Finset.univ widths g
    a = (∑ j, widths j * g j) / (ell / d) ∧ 0 ≤ a ∧ a ≤ delta / 2 ∧
    ∃ selected : Finset Slot, selected ⊆ main ∧ (∀ j ∈ selected, 0 < g j) ∧
      (∑ j ∈ selected, widths j) ≤ scheduledCapacity d v ∧
      a * scheduledCapacity d v - (delta / 2) * mesh ≤
        ∑ j ∈ selected, widths j * g j ∧
      ∀ U : ℝ, 1 ≤ U → ∀ Q : Slot → ℂ,
        (∀ j, 0 < g j → U ^ (2 * widths j * g j) ≤ ‖Q j‖ ^ 2) →
        U ^ (2 * a * scheduledCapacity d v - delta * mesh) ≤
          ‖∏ j ∈ selected, Q j‖ ^ 2 := by
  have hdpos := physical_d_pos hd.1
  have hell : 0 < ell := by linarith [Geometry.ell_pos,Geometry.ell_lt_fifth]
  have hL : 0 < ∑ j, widths j := by rw [hsum]; exact div_pos hell hdpos
  have hcap : scheduledCapacity d v ≤ ∑ j, widths j := by
    rw [hsum]
    exact scheduledCapacity_le_supply hd hv
  obtain ⟨ha, had⟩ := weightedMean_bounds Finset.univ widths g delta
    (fun j _ => hw j) hL (fun j _ => hg j)
  obtain ⟨T, _, hT, hTpos, hTcap, hgain, hspike⟩ := SlotSelection.zero_error_whole_slots
    Finset.univ main widths g delta mesh (scheduledCapacity d v)
    hdelta hmesh.le (fun j _ => hw j) (fun j _ => hwm j) hL
    (fun j _ => hg j) (fun j _ => herror j)
    (scheduledCapacity_nonneg hd hv) hcap
  refine ⟨?_, ha, had, T, hT, hTpos, hTcap, hgain, ?_⟩
  · unfold weightedMean
    rw [hsum]
  · intro U hU Q hQ
    exact hspike U hU Q (fun j _ => hQ j)

end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect

