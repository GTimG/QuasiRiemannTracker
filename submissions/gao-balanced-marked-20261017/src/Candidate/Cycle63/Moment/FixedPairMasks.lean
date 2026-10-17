import Candidate.Cycle63.Moment.CanonicalFirstMask
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical
open ActualEisensteinCubic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentFirstColumns
open CenteredMomentHeckeColumnWindow CenteredMomentFirstIdealFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentNaturalRowSource CenteredMomentChildRows RayFourExpansion
local notation "O" => HeckeFamily.O

variable {η : Character} {C D : Ideal O} {hC : Supported C}
  {E : Finset (CommonIndex C D)} {ξ₁ ξ₂ : RayCharacter}

/-- Recover the primary-element presentation from the height identity of
the exact fixed pair used by the physical source. -/
theorem fixed_pair_left_element (F : FixedPair η C D hC E ξ₁ ξ₂)
    (n : O) (hn : Supported (Ideal.span {n})) (hp : goodLambda^2∣n-1) :
    elementCoeff F.left n=elementCoeff η n*coprimalityMask fixedBadMask n*
      leftCoefficient (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)
        (activeConductor C D)
        (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*
      rayCharacter ξ₁ n := by
  have hn0 : n≠0 := Ideal.span_singleton_eq_bot.not.mp hn.1
  have hh := F.left_height (Ideal.span {n}) hn 0
  rw [rowWeight_one_primary η fixedBadMask 0 _ hn] at hh
  simp only [heightCoeff,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one,
    idealCoeff_span _ hn0,CompletedGauss.primaryGenerator_span n hn0 hp] at hh
  exact hh.trans (by ring)

theorem fixed_pair_right_element (F : FixedPair η C D hC E ξ₁ ξ₂)
    (n : O) (hn : Supported (Ideal.span {n})) (hp : goodLambda^2∣n-1) :
    elementCoeff F.right n=elementCoeff η n*coprimalityMask fixedBadMask n*
      rightCoefficient (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)
        (activeConductor C D)
        (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*
      rayCharacter ξ₂ n := by
  have hn0 : n≠0 := Ideal.span_singleton_eq_bot.not.mp hn.1
  have hh := F.right_height (Ideal.span {n}) hn 0
  rw [rowWeight_one_primary η fixedBadMask 0 _ hn] at hh
  simp only [heightCoeff,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one,
    idealCoeff_span _ hn0,CompletedGauss.primaryGenerator_span n hn0 hp] at hh
  exact hh.trans (by ring)

/-- The actual physical pair, rather than a separately chosen pair, has
the fixed-parent natural-row masks needed by the joint dictionary. -/
theorem fixed_pair_left_natural_mask (η₀ : Character) (u₀ : O)
    (F₀ : NaturalRow η₀ u₀) (R : Ideal O)
    (F : FixedPair (excluded F₀.character R) C D hC E ξ₁ ξ₂) :
    ∃u : Oˣ,∀G : NaturalRow (childCharacter η₀
      (firstPhaseCharacter C D hC (activeExponent C D)*ξ₁))
      (u₀*(u:O)*primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*
        firstLeftUncancelled C D),
      ∀I : Ideal O,idealCoeff F.left I=
        if IsCoprime I F.left.modulus then idealCoeff G.character I else 0 := by
  obtain ⟨u,hu⟩ := actual_first_left_natural_parent_source_mask η₀ u₀ F₀ R fixedBadMask C D hC E ξ₁
  exact ⟨u,hu F.left F.left_modulus (fixed_pair_left_element F)⟩

theorem fixed_pair_right_natural_mask (η₀ : Character) (u₀ : O)
    (F₀ : NaturalRow η₀ u₀) (R : Ideal O)
    (F : FixedPair (excluded F₀.character R) C D hC E ξ₁ ξ₂) :
    ∃u : Oˣ,∀G : NaturalRow (childCharacter η₀
      (firstPhaseCharacter C D hC (fun P=>6-activeExponent C D P)*ξ₂))
      (u₀*(u:O)*primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*
        firstRightUncancelled C D),
      ∀I : Ideal O,idealCoeff F.right I=
        if IsCoprime I F.right.modulus then idealCoeff G.character I else 0 := by
  obtain ⟨u,hu⟩ := actual_first_right_natural_parent_source_mask η₀ u₀ F₀ R fixedBadMask C D hC E ξ₂
  exact ⟨u,hu F.right F.right_modulus (fixed_pair_right_element F)⟩

end
end OAI.SevenEighths.Cycle63Moment
#print axioms OAI.SevenEighths.Cycle63Moment.fixed_pair_left_element
#print axioms OAI.SevenEighths.Cycle63Moment.fixed_pair_right_element
#print axioms OAI.SevenEighths.Cycle63Moment.fixed_pair_left_natural_mask
#print axioms OAI.SevenEighths.Cycle63Moment.fixed_pair_right_natural_mask
