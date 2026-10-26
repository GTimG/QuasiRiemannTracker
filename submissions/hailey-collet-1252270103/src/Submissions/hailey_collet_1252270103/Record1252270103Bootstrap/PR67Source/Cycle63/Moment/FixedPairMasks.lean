import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.CanonicalFirstMask
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
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

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
