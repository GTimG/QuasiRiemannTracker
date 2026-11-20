/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Rounded physical whole-slot quotas for the actual P4 ordinary cap. -/
import Candidate.C092.transport.StrongPairOrdinaryBank
import Candidate.C092.transport.StrongPairOrdinaryPrice

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
open QRH.Cycle092.WholeSlot
open OAI OAI.SevenEighths HeckeFamily HeckeDetectorSupportedWitness

/-- Selection is made from physical widths d*w and the true strict source
quota. The retained set depends on this descriptor, not on any row or zero. -/
theorem ordinary_whole_quota {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (w : Slot→ℝ) {d quota rounding : ℝ} (hd : 0 < d) (hq : 0 ≤ quota)
    (hw : ∀ k,0 ≤ w k) (hwm : ∀ k,d*w k ≤ rounding) (hr : 0 ≤ rounding) :
    ∃ F : Finset Slot,(∑ k∈F,w k) ≤ quota ∧
      (∑ k∈Finset.univ\F,d*w k) ≤ max 0 ((∑ k,d*w k)-d*quota+rounding) ∧
      ((∑ k,d*w k) ≤ d*quota → F=Finset.univ) := by
  obtain ⟨F,hF,hrest,hexhaust⟩ := select_before_rows (fun k=>d*w k) rounding (d*quota)
    (fun k=>mul_nonneg hd.le (hw k)) hwm hr (mul_nonneg hd.le hq)
  refine ⟨F,?_,hrest,hexhaust⟩
  rw [←Finset.mul_sum] at hF
  exact (mul_le_mul_iff_right₀ hd).mp hF

/-- A genuine inverse-escaping witness is assigned an upward bank cap
through .51. Its own m is never changed in the P4 replacement exponent. -/
theorem ordinary_actual_cap_selection {Label : Type*} {χ : Label→Character}
    {Z a ε T allowance m0 δ : ℝ} {i : ℕ}
    (c : Cutoff) (w : SupportedWitness χ Z a ε (totalCutoff c) T allowance i)
    (bank : Finset ℝ)
    (hnet : ∀ m : ℝ,m0 ≤ m → m ≤ 51/100 → ∃ B∈bank,m ≤ B ∧ B-m < δ)
    (hm0 : m0 ≤ (c.ordinary:ℝ)) {b : ℚ} (hg : CutoffGuard b c)
    (hε : ε ≤ 1/7500) :
    ∃ B∈bank,collaredOrdinaryCap c w.m ≤ B ∧ B-collaredOrdinaryCap c w.m < δ := by
  exact hnet _ (hm0.trans (le_max_right _ _)) (actual_ordinary_cap_upper c w hg hε)

#print axioms ordinary_whole_quota
#print axioms ordinary_actual_cap_selection
end
end QRH.Cycle092.StrongPair
