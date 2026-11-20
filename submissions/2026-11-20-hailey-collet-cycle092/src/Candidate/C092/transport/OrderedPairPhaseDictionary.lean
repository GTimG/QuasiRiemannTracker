/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The corrected signed comparison is exactly the physical zero-height source
with independently normPowerProfile-twisted original ordinary tests. -/
import Candidate.C092.transport.OrderedPairPhaseAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.OrderedPairPhase
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentSecondHeightFamily
open CenteredMomentLattice
open QRH.Cycle092.StrongPair QRH.Cycle092.ReferenceShortP3

/-- Exact complex signed dictionary at the coefficient convention +I*t.
After EACH arm's own phase is removed, the source has coefficients 1 and -1
on the two equal-product rectangles, with no residual X/Y norm phases. -/
theorem alignedPair_eq_profile_signed {ι : Type} (T : Finset ι) (η₁ η₂ : Character)
    (W₁ W₂ : ℝ→ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ) (mark : ι→FreeRow→ℂ) (u : FreeRow)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hprod : Y₁*Y₂=X₁*X₂) :
    alignedPairOn T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ Y₁ Y₂ mark u =
      signedPairOn T η₁ η₂ (normPowerProfile W₁ a b ha hs₁ hW₁ t₁)
        (normPowerProfile W₂ a b ha hs₂ hW₂ t₂) 0 0 X₁ X₂ Y₁ Y₂ mark u := by
  unfold alignedPairOn
  rw [alignedRow_eq_profile T η₁ η₂ W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ t₁ t₂ X₁ X₂ mark u hX₁ hX₂,
    alignedRow_eq_profile T η₁ η₂ W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ t₁ t₂ Y₁ Y₂ mark u hY₁ hY₂]
  exact pairRow_sub_eq_signed T η₁ η₂ _ _ 0 0 X₁ X₂ Y₁ Y₂ mark u hX₁.le hX₂.le hY₁.le hY₂.le hprod

/-- Same original finite rows, common marks and exact root normalizer.
The transformed profiles do not alter either original uncentered energy. -/
theorem alignedEnergy_eq_profile_signedEnergy {ι : Type} (T : Finset ι) (rows : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ) (mark : ι→FreeRow→ℂ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hprod : Y₁*Y₂=X₁*X₂) :
    alignedPairEnergyOn T rows η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ Y₁ Y₂ mark =
      signedPairEnergyOn T rows η₁ η₂ (normPowerProfile W₁ a b ha hs₁ hW₁ t₁)
        (normPowerProfile W₂ a b ha hs₂ hW₂ t₂) 0 0 X₁ X₂ Y₁ Y₂ mark := by
  unfold alignedPairEnergyOn signedPairEnergyOn
  apply Finset.sum_congr rfl
  intro u hu
  rw [alignedPair_eq_profile_signed T η₁ η₂ W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂
    t₁ t₂ X₁ X₂ Y₁ Y₂ mark u hX₁ hX₂ hY₁ hY₂ hprod]

#print axioms alignedPair_eq_profile_signed
#print axioms alignedEnergy_eq_profile_signedEnergy
end
end QRH.Cycle092.OrderedPairPhase
