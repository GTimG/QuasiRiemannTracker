import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQSaved
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceLowerSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalSaved
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCommonSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPhysicalSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondEnergySplit CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondHeightFamily CenteredMomentChildRows RayFourExpansion
open CenteredMomentRestrictedEnergy
open CenteredExceptionalProfile CenteredMomentExceptionalReflection
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFiniteProfileExceptional CenteredMomentRankinRadical
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local instance geometryExceptionalSplitDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) :=
  Classical.decEq _

/-- The fixed-inducing filter does not choose one of the two ray characters
in the physical pair. Both changes of ray and the reflected row are exact. -/
theorem geometry_fixed_inducing_ray_iff (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)}) (m A z : O)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m) :
    FixedInducingRow (childCharacter η χ) Q m A z ↔
      FixedInducingRow (childCharacter η ξ) Q m A z := by
  constructor <;> intro h
  · have hh := fixedInducingRow_reflected η χ χ Q hQ m A z hml hm2 h
    simpa only [neg_neg] using
      fixedInducingRow_reflected η χ ξ Q hQ m A (-z) hml hm2 hh
  · have hh := fixedInducingRow_reflected η ξ ξ Q hQ m A z hml hm2 h
    simpa only [neg_neg] using
      fixedInducingRow_reflected η ξ χ Q hQ m A (-z) hml hm2 hh

theorem geometry_nonexceptional_pair (η : Character) (χ₀ χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)})
    (m : O) (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) (z : O)
    (hz : z∈partRows false η χ₀ Q m C D U R) :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ∧
      nonexceptional η (ξ⁻¹) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) (-z) := by
  rw [partRows_false] at hz
  obtain ⟨hs,hn⟩ := Finset.mem_filter.mp hz
  have hz0 := sourceRows_nonzero C D U R z hs
  refine ⟨⟨hz0,?_⟩,⟨neg_ne_zero.mpr hz0,?_⟩⟩
  · exact fun h => hn ((geometry_fixed_inducing_ray_iff η χ₀ χ Q hQ m _ z hml hm2).mpr h)
  · exact (not_fixedInducingRow_reflection_iff η χ₀ (ξ⁻¹) Q hQ m _ z hml hm2).mp hn

theorem geometry_nonexceptional_reduced_pair (η : Character) (χ₀ χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (τ : RayCharacter→ Character)
    (hf : Family η C D hC hD U τ) (R : ℝ) (z : O)
    (hz : z∈partRows false η χ₀ Q m C D U R) :
    (z≠0 ∧ ¬FixedInducingRow (τ χ) Q fixedBadMask 1 z) ∧
      ((-z)≠0 ∧ ¬FixedInducingRow (τ (ξ⁻¹)) Q fixedBadMask 1 (-z)) := by
  have hp := geometry_nonexceptional_pair η χ₀ χ ξ Q hQ m hml hm2 C D U R z hz
  exact ⟨(hf.nonexceptional_iff χ Q m z hm hml hm2).mp hp.1,
    (hf.nonexceptional_iff (ξ⁻¹) Q m (-z) hm hml hm2).mp hp.2⟩

/-- This split is linear before taking norms, so any moving scalar remains
inside its own physical block. -/
theorem geometry_physical_block_split (η : Character) (χ : RayCharacter)
    (Q : Ideal O) (m : O) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (W : 𝓢(ℝ,ℂ))
    (K : ℝ) (n : Fin 4→ℤ) :
    physicalBlock η t S β C D hC hD U R (sourceRows C D U R) W K n =
      physicalBlock η t S β C D hC hD U R (partRows true η χ Q m C D U R) W K n +
      physicalBlock η t S β C D hC hD U R (partRows false η χ Q m C D U R) W K n := by
  rw [partRows_false]
  exact physicalBlock_filter_split η t S β C D hC hD U R _ W K n _

attribute [local irreducible] physicalBlock

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
