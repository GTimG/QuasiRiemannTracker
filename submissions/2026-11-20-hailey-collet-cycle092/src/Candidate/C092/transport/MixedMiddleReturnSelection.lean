/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Saturate the genuine P.1 width using ONLY complementary original main slots;
the original count still retains its full amplitude-class mean. -/
import Candidate.C092.transport.MixedPacketWitnessMarks
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.SourceSelection

set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorPhysicalSelection HeckePrimeAmplitudeBins
open Cycle25.Numerator Cycle25DetectorRowCount
local notation "O" => HeckeFamily.O

/-- Whole-slot source selection uses the exact original error mask. Zero-gain
error slots remain in the denominator; the strongest count keeps F.q. -/
theorem saturated_main_selection {Slot : Type} [DecidableEq Slot]
    {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label : Type}
    {U a ε cutoff T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε cutoff T allowance i)
    (hU : 1<U) (ha : 1/2≤a) (main : Finset Slot) (hmain : main⊆F.slots)
    (l : ℝ) (hl : 0≤l) (hlL : l≤∑s∈F.slots,F.widths s) :
    let qMain := weightedMean F.slots F.widths (maskedGain main F.bin)
    0≤qMain ∧ qMain≤F.q ∧
    ∃selected : Finset Slot,selected⊆F.slots ∧ selected⊆main ∧
      (∑s∈selected,F.widths s)≤l ∧
      ∀u∈F.rows,U^(qMain*l-(2*a-1)*F.mesh/2)≤‖F.physicalProduct selected u‖ := by
  classical
  dsimp only
  let δ := 2*a-1
  let g := maskedGain main F.bin
  have hδ : 0≤δ := by dsimp [δ];linarith
  have hL : 0<∑s∈F.slots,F.widths s := (by norm_num : (0:ℝ)<7/37).trans_le F.supply
  obtain ⟨u0,hu0⟩ := F.nonempty
  have hgfull (s : Slot) (hs : s∈F.slots) : 0≤F.bin s ∧ F.bin s≤δ/2 := by
    rw [←F.fixed_bin u0 hu0 s hs]
    exact amplitude_bounds _ _ _ _ (by dsimp [δ] at hδ;linarith)
  have hg (s : Slot) (hs : s∈F.slots) : 0≤g s ∧ g s≤δ/2 := by
    dsimp [g,maskedGain]
    split_ifs
    · exact hgfull s hs
    · exact ⟨le_rfl,by positivity⟩
  have hq0 := (weightedMean_bounds F.slots F.widths g δ
    (fun s hs=>(F.widths_pos s hs).le) hL hg).1
  have hq : weightedMean F.slots F.widths g≤F.q := by
    unfold weightedMean Fiber.q
    apply div_le_div_of_nonneg_right _ hL.le
    apply Finset.sum_le_sum
    intro s hs
    apply mul_le_mul_of_nonneg_left _ (F.widths_pos s hs).le
    dsimp [g,maskedGain]
    split_ifs
    · exact le_rfl
    · exact (hgfull s hs).1
  obtain ⟨sel,hsub,hm,hpos,hlen,hgain,hspike⟩ := SlotSelection.zero_error_whole_slots
    F.slots main F.widths g δ F.mesh l hδ F.mesh_nonneg
    (fun s hs=>(F.widths_pos s hs).le) F.widths_mesh hL hg
    (fun s hs hn=>by simp [g,maskedGain,hn]) hl hlL
  refine ⟨hq0,hq,sel,hsub,hm,hlen,?_⟩
  intro u hu
  have hb := hspike U hU.le
    (fun s=>physical M H (fun v : FreeRow=>v.val) F.profile F.upper F.widths F.external U u s) (by
      intro s hs hgs
      have hms : s∈main := by
        by_contra hn
        simp [g,maskedGain,hn] at hgs
      have he : g s=F.bin s := by simp [g,maskedGain,hms]
      rw [he] at hgs ⊢
      have hsbin := F.fixed_bin u hu s hs
      rw [←hsbin] at hgs ⊢
      exact squared_spike U (F.widths s) (δ/2) F.binWidth _ hU (F.widths_pos s hs) F.binWidth_pos hgs)
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (zero_lt_one.trans hU).le _)
    (norm_nonneg _) (by norm_num : (2:ℕ)≠0)).mp
  have hp : (U^(weightedMean F.slots F.widths g*l-δ*F.mesh/2))^2 =
      U^(2*weightedMean F.slots F.widths g*l-δ*F.mesh) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (zero_lt_one.trans hU).le]
    congr 1
    ring
  rw [hp]
  exact hb

#print axioms saturated_main_selection
end
end QRH.Cycle092.MixedMiddleReturn
