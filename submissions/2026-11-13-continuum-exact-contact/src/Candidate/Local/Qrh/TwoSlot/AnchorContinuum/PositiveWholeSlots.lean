/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Actual amplitude-class whole-slot selection at variable physical capacity.
Adapted from PR137 SourceSelection (Sil and predecessor authors, Apache-2.0).
Error slots have zero gain only in the selection mean; no row is discarded. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveSelected
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.SourceSelection

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open OAI OAI.SevenEighths HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorFiberPartition ProbeHighRowFamily Cycle25ProbeFinalAssembly Cycle25DetectorRowCount
open ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle25.Numerator
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

theorem capacity_le_supply {cost d v : ℝ} (hd : 0 < d) (hdhi : d ≤ 1) :
    Selection.scheduledCapacity cost d v ≤ Geometry.ell/d := by
  have hcap : (3/40:ℝ) ≤ Geometry.ell/d := by
    apply (le_div_iff₀ hd).mpr
    linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds.ell_interval.1]
  unfold Selection.scheduledCapacity Selection.clippedCapacity
  apply max_le
  · exact div_nonneg Geometry.ell_pos.le hd.le
  · exact (min_le_left _ _).trans hcap

theorem scheduled_whole_slots (A : ChosenData) (cost d v delta : ℝ)
    (hd : d ∈ Set.Icc (1/200:ℝ) 1) (hdelta : 0 ≤ delta)
    (main : Finset (Fin A.D.N)) (g : Fin A.D.N → ℝ)
    (hg : ∀ j, 0 ≤ g j ∧ g j ≤ delta/2) (herror : ∀ j, j ∉ main → g j = 0) :
    let widths := fun j => A.D.length j/d
    let q := weightedMean Finset.univ widths g
    0 ≤ q ∧ q ≤ delta/2 ∧ ∃ selected : Finset (Fin A.D.N),
      selected ⊆ main ∧ (∀ j ∈ selected, 0 < g j) ∧
      (∑ j ∈ selected, widths j) ≤ Selection.scheduledCapacity cost d v ∧
      ∀ U : ℝ, 1 ≤ U → ∀ Q : Fin A.D.N → ℂ,
        (∀ j, 0 < g j → U^(2*widths j*g j) ≤ ‖Q j‖^2) →
        U^(2*q*Selection.scheduledCapacity cost d v-delta*Cycle25.sourceMesh A.D.t) ≤
          ‖∏ j ∈ selected, Q j‖^2 := by
  have hdpos : 0 < d := by linarith [hd.1]
  let widths := fun j => A.D.length j/d
  have hsum : (∑ j, widths j) = Geometry.ell/d := by
    dsimp [widths]
    rw [←Finset.sum_div,A.D.slots_sum]
  have hL : 0 < ∑ j, widths j := by rw [hsum]; exact div_pos Geometry.ell_pos hdpos
  have hw (j : Fin A.D.N) : 0 ≤ widths j := (div_pos (A.D.slots_pos j) hdpos).le
  have hm := Cycle25.sourceMesh_pos A.D.t_pos
  have hwm (j : Fin A.D.N) : widths j ≤ Cycle25.sourceMesh A.D.t :=
    rescaled_slot_mesh A.D.length (Cycle25.sourceMesh A.D.t) d hd.1 hm.le A.fine j
  have hcap : Selection.scheduledCapacity cost d v ≤ ∑ j, widths j := by
    rw [hsum]
    exact capacity_le_supply hdpos hd.2
  obtain ⟨hq,hqtop⟩ := weightedMean_bounds Finset.univ widths g delta
    (fun j _ => hw j) hL (fun j _ => hg j)
  obtain ⟨T,_,hT,hTpos,hTcap,_hgain,hspike⟩ := SlotSelection.zero_error_whole_slots
    Finset.univ main widths g delta (Cycle25.sourceMesh A.D.t)
    (Selection.scheduledCapacity cost d v) hdelta hm.le (fun j _ => hw j)
    (fun j _ => hwm j) hL (fun j _ => hg j) (fun j _ => herror j)
    (le_max_left _ _) hcap
  exact ⟨hq,hqtop,T,hT,hTpos,hTcap,fun U hU Q hQ => hspike U hU Q (fun j _ => hQ j)⟩

theorem class_main_selection (A : ChosenData) (cost Z d v delta : ℝ)
    (hZ : 1 < Z) (hd : d ∈ Set.Icc (1/200:ℝ) 1) (hdelta : 0 ≤ delta)
    (z : ℂ) (rows : Finset FreeRow) (main : Finset (Fin A.D.N))
    (bin : BinLabel (Finset.univ : Finset (Fin A.D.N)) (delta/2) A.D.t)
    (hne : (amplitudeRows rows Finset.univ (Z^d) (delta/2) A.D.t A.D.t_pos
      (fun j => A.D.length j/d)
      (fun u j => HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val A.F.W
        2 (Z^(A.D.length j)) z) bin).Nonempty) :
    let Q := fun (u : FreeRow) j => HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val
      A.F.W 2 (Z^(A.D.length j)) z
    let rows' := amplitudeRows rows Finset.univ (Z^d) (delta/2) A.D.t A.D.t_pos
      (fun j => A.D.length j/d) Q bin
    let g := binValue Finset.univ (delta/2) A.D.t bin
    let q := weightedMean Finset.univ (fun j => A.D.length j/d) (maskedGain main g)
    0 ≤ q ∧ q ≤ delta/2 ∧ ∃ selected : Finset (Fin A.D.N), selected ⊆ main ∧
      (∑ j ∈ selected, A.D.length j/d) ≤ Selection.scheduledCapacity cost d v ∧
      ∀ u ∈ rows',
        (Z^d)^(2*q*Selection.scheduledCapacity cost d v-delta*Cycle25.sourceMesh A.D.t) ≤
          ‖∏ j ∈ selected, Q u j‖^2 ∧
        ((∀ j, ‖Q u j‖ ≤ (Z^(A.D.length j))^
          (HeckePrimeAmplitudeBins.amplitude (Z^(A.D.length j)) (delta/2) A.D.t (Q u j)+A.D.t)) →
          ‖∏ j ∈ main, Q u j‖ ≤ (Z^d)^(q*(Geometry.ell/d)+A.D.t*(Geometry.ell/d))) := by
  dsimp only
  let Q := fun (u : FreeRow) j => HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val
    A.F.W 2 (Z^(A.D.length j)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) (delta/2) A.D.t A.D.t_pos
    (fun j => A.D.length j/d) Q bin
  let g := binValue Finset.univ (delta/2) A.D.t bin
  have hdpos : 0 < d := by linarith [hd.1]
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hdpos
  have hscale (j : Fin A.D.N) : (Z^d)^(A.D.length j/d) = Z^(A.D.length j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hgfull : ∀ j, 0 ≤ g j ∧ g j ≤ delta/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j
    have he := amplitude_class_value rows Finset.univ (Z^d) (delta/2) A.D.t A.D.t_pos
      (fun j => A.D.length j/d) Q bin u hu j (Finset.mem_univ j)
    dsimp only [g]
    rw [←he]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  have hg : ∀ j, 0 ≤ maskedGain main g j ∧ maskedGain main g j ≤ delta/2 := by
    intro j
    unfold maskedGain
    split_ifs
    · exact hgfull j
    · exact ⟨le_rfl,by positivity⟩
  obtain ⟨hq0,hqtop,T,hT,hTpos,hTcap,hspike⟩ := scheduled_whole_slots A cost d v delta
    hd hdelta main (maskedGain main g) hg (fun j hj => by simp [maskedGain,hj])
  refine ⟨hq0,hqtop,T,hT,hTcap,?_⟩
  intro u hu
  have hgrow (j : Fin A.D.N) :
      HeckePrimeAmplitudeBins.amplitude (Z^(A.D.length j)) (delta/2) A.D.t (Q u j) = g j := by
    have he := amplitude_class_value rows Finset.univ (Z^d) (delta/2) A.D.t A.D.t_pos
      (fun j => A.D.length j/d) Q bin u hu j (Finset.mem_univ j)
    simpa only [hscale] using he
  refine ⟨?_,?_⟩
  · apply hspike (Z^d) hU.le (Q u)
    intro j hj
    have hjmain : j ∈ main := by
      by_contra hm
      simp only [maskedGain,ite_eq_right hm,lt_self_iff_false] at hj
    have hgm : maskedGain main g j = g j := by simp [maskedGain,hjmain]
    have hpos : 0 < HeckePrimeAmplitudeBins.amplitude ((Z^d)^(A.D.length j/d))
        (delta/2) A.D.t (Q u j) := by
      rw [hscale,hgrow]
      rwa [hgm] at hj
    have hh := HeckePrimeAmplitudeBins.squared_spike (Z^d) (A.D.length j/d) (delta/2) A.D.t
      (Q u j) hU (div_pos (A.D.slots_pos j) hdpos) A.D.t_pos hpos
    simpa only [hscale,hgrow,hgm] using hh
  · intro hupper
    have hL : (∑ j, A.D.length j/d) = Geometry.ell/d := by rw [←Finset.sum_div,A.D.slots_sum]
    have hh := masked_main_product_upper main (fun j => A.D.length j/d) g (Z^d) A.D.t (Q u)
      hU.le A.D.t_pos.le (fun j => (div_pos (A.D.slots_pos j) hdpos).le)
      (by rw [hL]; exact div_pos Geometry.ell_pos hdpos) (by
        intro j hj
        calc
          _ ≤ (Z^(A.D.length j))^(g j+A.D.t) := by
            have he := hupper j
            change ‖Q u j‖ ≤ (Z^(A.D.length j))^
              (HeckePrimeAmplitudeBins.amplitude (Z^(A.D.length j)) (delta/2) A.D.t (Q u j)+A.D.t) at he
            rwa [hgrow] at he
          _ = _ := by rw [←hscale j,←Real.rpow_mul (by positivity)])
    simpa only [hL] using hh

theorem selected_product_crude (A : ChosenData) (Z d delta : ℝ)
    (hZ : 1 < Z) (hd : (1/2:ℝ) ≤ d) (hdelta : 0 ≤ delta) (hdeltahi : delta ≤ 3/4)
    (selected : Finset (Fin A.D.N)) (Q : Fin A.D.N → ℂ)
    (hQ : ∀ j, ‖Q j‖ ≤ (Z^(A.D.length j))^
      (HeckePrimeAmplitudeBins.amplitude (Z^(A.D.length j)) (delta/2) A.D.t (Q j)+A.D.t)) :
    ‖∏ j ∈ selected, Q j‖ ≤ Z^d := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have ht := A.D.t_pos
  have hlength : ∑ j ∈ selected, A.D.length j ≤ (1/5:ℝ) := by
    apply le_trans _ Geometry.ell_lt_fifth.le
    rw [←A.D.slots_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
      (fun j _ _ => (A.D.slots_pos j).le)
  calc
    _ ≤ ∏ j ∈ selected, Z^(A.D.length j*(delta/2+A.D.t)) := by
      rw [norm_prod]
      apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
      intro j hj
      have ha := (HeckePrimeAmplitudeBins.amplitude_bounds
        (Z^(A.D.length j)) (delta/2) A.D.t (Q j) (by positivity)).2
      apply (hQ j).trans
      rw [←Real.rpow_mul hZ0.le]
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      exact mul_le_mul_of_nonneg_left (by linarith :
        HeckePrimeAmplitudeBins.amplitude (Z^(A.D.length j)) (delta/2) A.D.t (Q j)+A.D.t ≤
          delta/2+A.D.t) (A.D.slots_pos j).le
    _ = Z^((∑ j ∈ selected, A.D.length j)*(delta/2+A.D.t)) := by
      rw [←Real.rpow_sum_of_pos hZ0,←Finset.sum_mul]
    _ ≤ Z^d := by
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      have hh := mul_le_mul_of_nonneg_right hlength (by positivity : 0 ≤ delta/2+A.D.t)
      nlinarith only [hh,hdeltahi,A.D.t_small,hd]

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.scheduled_whole_slots
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.class_main_selection
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.selected_product_crude
