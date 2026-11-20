/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual supported ordinary witnesses choose genuine bank radii and whole slots.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafOrdinary
import Candidate.C092.transport.StrongPairOrdinarySelection
set_option autoImplicit false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeDetectorSupportedWitness
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
open QRH.Cycle092.StrongPair QRH.Cycle092.LowActual

/-- The same actual witness chooses a native bank member and a whole-slot
quota. The retained subset is selected from its physical widths before rows. -/
theorem terminal_ordinary_witness_selection {Label Slot : Type} [Fintype Slot] [DecidableEq Slot]
    {χ : Label → Character} {Z a epsilon T allowance n m0 gap d rounding : ℝ} {i : ℕ}
    (c : Cutoff) (witness : SupportedWitness χ Z a epsilon (totalCutoff c) T allowance i)
    (bank : Finset (ℝ×ℝ)) (dec : (ℝ×ℝ) → ℝ)
    (hbank : ∀ B ∈ bank,(98/100:ℝ) ≤ B.1 ∧ B.1 ≤ (H:ℝ) ∧ m0 ≤ B.2 ∧ B.2 ≤ 51/100 ∧
      0 < dec B ∧ dec B ≤ gap ∧ 0 < nearOrdinaryQuota n B.2 B.1-dec B)
    (hnet : ∀ d m : ℝ,(98/100:ℝ) ≤ d  →  m0 ≤ m  →  m ≤ 51/100  → 
      ∃ B ∈ bank,B.1 ≤ min d (H:ℝ) ∧ min d (H:ℝ)-B.1 < gap ∧ m ≤ B.2 ∧ B.2-m < gap)
    (hd : (98/100:ℝ) ≤ d) (hm0 : m0 ≤ (c.ordinary:ℝ)) {b : ℚ}
    (hg : CutoffGuard b c) (he : epsilon ≤ 1/7500)
    (width : Slot → ℝ) (hw : ∀ k,0 ≤ width k) (hwm : ∀ k,d*width k ≤ rounding)
    (hr : 0 ≤ rounding) :
    ∃ B ∈ bank,∃ F : Finset Slot,
      (98/100:ℝ) ≤ B.1 ∧ B.1 ≤ min d (H:ℝ) ∧ min d (H:ℝ)-B.1 < gap ∧
      collaredOrdinaryCap c witness.m ≤ B.2 ∧ B.2-collaredOrdinaryCap c witness.m < gap ∧
      0 < dec B ∧ dec B ≤ gap ∧ 0 < nearOrdinaryQuota n B.2 B.1-dec B ∧
      (∑k ∈ F,width k) ≤ nearOrdinaryQuota n B.2 B.1-dec B ∧
      (∑k ∈ Finset.univ\F,d*width k) ≤ 
        max 0 ((∑k,d*width k)-d*(nearOrdinaryQuota n B.2 B.1-dec B)+rounding) ∧
      ((∑k,d*width k) ≤ d*(nearOrdinaryQuota n B.2 B.1-dec B)  →  F=Finset.univ) := by
  obtain ⟨B,hB,hradius,hgap,hcap,hcapgap⟩:=hnet d (collaredOrdinaryCap c witness.m) hd
    (hm0.trans (le_max_right _ _)) (actual_ordinary_cap_upper c witness hg he)
  obtain ⟨hB0,hBH,hBm0,hBm1,hdec,hdecgap,hquota⟩:=hbank B hB
  obtain ⟨F,hF,hrest,hex⟩:=ordinary_whole_quota width (by linarith : 0 < d) hquota.le hw hwm hr
  exact ⟨B,hB,F,hB0,hradius,hgap,hcap,hcapgap,hdec,hdecgap,hquota,hF,hrest,hex⟩

/-- A genuine measured upper window supplies the individual bounds on all
removed original whole slots, retaining the same payment and zero widths. -/
theorem terminal_ordinary_removed_slots {Slot : Type} [Fintype Slot]
    {U pay upper : ℝ} (width : Slot → ℝ) (mark : Slot → ℂ)
    (hU : 1 < U) (hpay : 0 < pay) (hw : ∀ k,0 ≤ width k) (he : 0 ≤ upper)
    (hz : ∀ k,width k=0  →  ‖mark k‖^2 ≤ pay)
    (hresponse : response U pay width (fun k=>‖mark k‖^2) ≤ upper) :
    ∀ k,‖mark k‖^2 ≤ pay*U^(upper*width k) :=
  (response_le_iff_amplitudes width (fun k=>‖mark k‖^2) hU hpay hw (fun k=>sq_nonneg _) hz he).mp hresponse

#print axioms terminal_ordinary_witness_selection
#print axioms terminal_ordinary_removed_slots
end
end QRH.Cycle092.RegularColoredForward
