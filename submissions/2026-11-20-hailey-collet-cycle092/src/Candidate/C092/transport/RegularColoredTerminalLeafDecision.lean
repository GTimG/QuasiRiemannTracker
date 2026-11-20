/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual class decisions retain the supported inverse dyad and genuine bank.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafTicketGuards
import Candidate.C092.transport.MediumInversePriceSourceBank
set_option autoImplicit false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open QRH.Cycle092.Source
open Qrh.MarkedAnchor.Interface

/-- A genuine finite rectangle bank decides the two actual inverse arms.
The original inverse length is retained, including its full r>1 collar. -/
theorem terminal_actual_inverse_decision {J : ℕ} (bank : Fin J → Contract.AnchorRect)
    (zeta r : ℝ) (hr : 367/500 ≤ r)
    (cover : ∀r : ℝ,367/500 ≤ r  →  r ≤ 1  →  inverseQuota r ≤ zeta ∨
      (0 ≤ inverseQuota r-zeta  →  ∃j,(bank j).Admissible r (inverseQuota r-zeta) 1)) :
    (1 < r) ∨ (r ≤ 1 ∧ inverseQuota r ≤ zeta) ∨
      (r ≤ 1 ∧ zeta < inverseQuota r ∧ ∃j,(bank j).Admissible r (inverseQuota r-zeta) 1) := by
  by_cases hlarge : 1 < r
  · exact Or.inl hlarge
  · have hr1 : r ≤ 1 := le_of_not_gt hlarge
    rcases cover r hr hr1 with hsmall|hadmissible
    · exact Or.inr (Or.inl ⟨hr1,hsmall⟩)
    · by_cases hsmall : inverseQuota r ≤ zeta
      · exact Or.inr (Or.inl ⟨hr1,hsmall⟩)
      · have hz : zeta < inverseQuota r := lt_of_not_ge hsmall
        exact Or.inr (Or.inr ⟨hr1,hz,hadmissible (sub_nonneg.mpr hz.le)⟩)

/-- The native unmarked implication is paid in both exhausted inverse
cases; no positive selected width is requested when the quota vanishes. -/
theorem terminal_actual_unmarked_guard {r zeta fee : ℝ} (hz : zeta ≤ fee)
    (h : 1 < r ∨ (r ≤ 1 ∧ inverseQuota r ≤ zeta)) :
    r ≤ 1  →  inverseQuota r ≤ fee := by
  intro hr
  rcases h with hlarge|hsmall
  · exact False.elim (not_le.mpr hlarge hr)
  · exact hsmall.2.trans hz

/-- The same literal supported dyad decides ordinary versus inverse on
ALL members of the class, without selecting another witness or zero. -/
theorem terminal_fixed_inverse_cutoff {Label : Type} [Fintype Label]
    (rows : Finset FreeRow) (χ : FreeRow → Label → Character)
    (Z a epsilon cutoff T allowance inverse : ℝ) (i : ℕ)
    (ws : ∀u : rows,SupportedWitness (χ u.val) Z a epsilon cutoff T allowance i)
    (r : ℝ) (hr : ∀u,(ws u).r=r) :
    (r < inverse ∧ ∀u,(ws u).r < inverse) ∨
      (inverse ≤ r ∧ ∀u,inverse ≤ (ws u).r) := by
  by_cases h : r < inverse
  · exact Or.inl ⟨h,fun u=>(hr u).trans_lt h⟩
  · exact Or.inr ⟨le_of_not_gt h,fun u=>(le_of_not_gt h).trans_eq (hr u).symm⟩

#print axioms terminal_actual_inverse_decision
#print axioms terminal_actual_unmarked_guard
#print axioms terminal_fixed_inverse_cutoff
end
end QRH.Cycle092.RegularColoredForward
