/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Same-row P.3 joins. Analytic fourth estimates are explicit premises here;
the complete native short Input supplier is ReferenceShortP3Poisson. -/
import Candidate.C092.transport.StrongPairFinite
import Candidate.C092.transport.ReferenceShortP3Geometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ReferenceShortP3
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open ConcretePrimeRowBridge HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.StrongPair
open QRH.Cycle092.OrdinaryColumn

/-- All original marks are placed in the genuine short fourth; the
independently twisted companion is entirely unmarked. No row restriction,
character, height, profile or numerator is replaced by this Cauchy join. -/
theorem finite_reference_of_fourths {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (T : Finset Slot) (s : Finset FreeRow) (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (mark : Slot → FreeRow → ℂ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hshort : (∑ u∈s,
      (‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁‖^2 *
        ∏ i∈T, ‖mark i u‖^2)^2) ≤ A^2)
    (hcompanion : (∑ u∈s,
      ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂‖^4) ≤ B^2) :
    finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤ A*B := by
  have h := finite_split_cauchy_on T T (Finset.Subset.refl _) s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark
  have hc : (∑ u∈s,
      (‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂‖^2 *
        ∏ i∈T\T, ‖mark i u‖^2)^2) ≤ B^2 := by
    simpa only [Finset.sdiff_self,Finset.prod_empty,mul_one,←pow_mul,
      show (2:ℕ)*2=4 from rfl] using hcompanion
  exact h.trans (mul_le_mul (Real.sqrt_le_iff.mpr ⟨hA,hshort⟩)
    (Real.sqrt_le_iff.mpr ⟨hB,hc⟩) (Real.sqrt_nonneg _) hA)

/-- The signed centered square is joined only after both the original
reference and the true centered energy have been bounded. Complex outside
phases stay inside the two literal amplitudes. -/
theorem finite_uncentered_of_centered {α : Type*} (s : Finset α)
    (row reference : α → ℂ) {C R : ℝ}
    (hcenter : (∑ u∈s, ‖row u-reference u‖^2) ≤ C)
    (href : (∑ u∈s, ‖reference u‖^2) ≤ R) :
    (∑ u∈s, ‖row u‖^2) ≤ 2*C+2*R := by
  have hp (u : α) : ‖row u‖^2 ≤ 2*‖row u-reference u‖^2+2*‖reference u‖^2 := by
    have hn := norm_sub_le (row u-reference u) (-reference u)
    simp only [sub_neg_eq_add,norm_neg,sub_add_cancel] at hn
    have hnn : 0 ≤ ‖row u‖ := norm_nonneg _
    have hdiff : 0 ≤ (‖row u-reference u‖-‖reference u‖)^2 := sq_nonneg _
    nlinarith [sq_nonneg (‖row u-reference u‖+‖reference u‖-‖row u‖)]
  have hs := Finset.sum_le_sum (fun u (_ : u∈s) => hp u)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hs
  linarith

#print axioms finite_reference_of_fourths
#print axioms finite_uncentered_of_centered
end
end QRH.Cycle092.ReferenceShortP3
