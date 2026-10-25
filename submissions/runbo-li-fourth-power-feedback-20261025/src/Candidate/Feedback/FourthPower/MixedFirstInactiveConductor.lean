/- Copyright (c) 2026 Sil. Apache-2.0.
The ACTUAL first inactive subset and active conductor have disjoint
prime supports. Their product divides the common radical once, so the
fixed first child characters cost at most either full common norm.

-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstDiscardedEnergy

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.MixedFirstInactiveConductor
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentFirstCanonicalAllowance CenteredMomentRankinRadical
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstPhysicalSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Membership in the actual inactive-subset sum is essential here.
For an arbitrary E, the two factors can overlap and the claim need not hold. -/
theorem inactive_active_span_dvd_radical (C D : Id)
    (E : Finset (CommonIndex C D)) (hE : E∈inactiveSubsets C D) :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*
      activeConductor C D}∣commonRadical C D := by
  have hsub : E⊆principalSupport (Finset.univ : Finset (CommonIndex C D))
      (leftExponent C D) (rightExponent C D) := Finset.mem_powerset.mp hE
  have hp : (∏P∈E,P.val)∣
      ∏P∈principalSupport (Finset.univ : Finset (CommonIndex C D))
        (leftExponent C D) (rightExponent C D),P.val :=
    Finset.prod_dvd_prod_of_subset E _ (fun P : CommonIndex C D=>P.val) hsub
  rw [←Ideal.span_singleton_mul_span_singleton,primeSubsetGenerator,span_idealGenerator,
    commonRadical_active_principal]
  simpa only [mul_comm] using mul_dvd_mul_left (Ideal.span {activeConductor C D}) hp

theorem inactive_active_span_dvd_both (C D : Id) (hC : C≠0) (hD : D≠0)
    (E : Finset (CommonIndex C D)) (hE : E∈inactiveSubsets C D) :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*
      activeConductor C D}∣C ∧
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*
      activeConductor C D}∣D := by
  have hs := inactive_active_span_dvd_radical C D E hE
  have hCD : commonRadical C D=commonRadical D C := by
    simp only [commonRadical,Finset.inter_comm]
  refine ⟨hs.trans ((commonRadical_dvd_commonPart C D).trans
    (commonPart_dvd C D hC)),?_⟩
  rw [hCD] at hs
  exact hs.trans ((commonRadical_dvd_commonPart D C).trans (commonPart_dvd D C hD))

/-- The exact fixed presentation cost has not been hidden in the
constant; the radical is paid once, uniformly in both ray characters. -/
theorem fixed_pair_radical_caps (η : Character) (C D : Id) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (hE : E∈inactiveSubsets C D)
    (χ ξ : RayCharacter) (F : FixedPair η C D hC E χ ξ) :
    (F.left.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      (commonRadical C D).absNorm ∧
    (F.right.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      (commonRadical C D).absNorm := by
  have hn := CenteredExceptionalCount.norm_le_of_dvd (commonRadical_ne_zero C D)
    (inactive_active_span_dvd_radical C D E hE)
  have hcost : 0≤fixedPresentationCost*(η.modulus.absNorm:ℝ) :=
    mul_nonneg fixedPresentationCost_pos.le (Nat.cast_nonneg _)
  have hnorm (τ : Character)
      (hτ : τ.modulus=η.modulus*Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}*
        Ideal.span {(72:O)}*Ideal.span {
          primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D}) :
      (τ.modulus.absNorm:ℝ)=fixedPresentationCost*(η.modulus.absNorm:ℝ)*
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*
          activeConductor C D}).absNorm := by
    rw [hτ]
    simp only [map_mul,Nat.cast_mul,fixedPresentationCost]
    ring
  constructor
  · rw [hnorm F.left F.left_modulus]
    exact mul_le_mul_of_nonneg_left hn hcost
  · rw [hnorm F.right F.right_modulus]
    exact mul_le_mul_of_nonneg_left hn hcost

/-- A single conductor cap is available for BOTH sides of the first
physical pair. This keeps the smaller full common norm, with no
replacement of a prime power by a radical upper-support cap. -/
theorem fixed_pair_common_caps (η : Character) (C D : Id) (hC : Supported C) (hD : D≠0)
    (E : Finset (CommonIndex C D)) (hE : E∈inactiveSubsets C D)
    (χ ξ : RayCharacter) (F : FixedPair η C D hC E χ ξ) :
    (F.left.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      min (C.absNorm:ℝ) (D.absNorm:ℝ) ∧
    (F.right.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      min (C.absNorm:ℝ) (D.absNorm:ℝ) := by
  have hleft : ((commonRadical C D).absNorm:ℝ)≤C.absNorm :=
    CenteredExceptionalCount.norm_le_of_dvd hC.1
      ((commonRadical_dvd_commonPart C D).trans (commonPart_dvd C D hC.1))
  have hright : ((commonRadical C D).absNorm:ℝ)≤D.absNorm := by
    have he : commonRadical C D=commonRadical D C := by
      simp only [commonRadical,Finset.inter_comm]
    rw [he]
    exact CenteredExceptionalCount.norm_le_of_dvd hD
      ((commonRadical_dvd_commonPart D C).trans (commonPart_dvd D C hD))
  have hrad : ((commonRadical C D).absNorm:ℝ)≤min (C.absNorm:ℝ) (D.absNorm:ℝ) :=
    le_min hleft hright
  have hcost : 0≤fixedPresentationCost*(η.modulus.absNorm:ℝ) :=
    mul_nonneg fixedPresentationCost_pos.le (Nat.cast_nonneg _)
  have hc := fixed_pair_radical_caps η C D hC E hE χ ξ F
  exact ⟨hc.1.trans (mul_le_mul_of_nonneg_left hrad hcost),
    hc.2.trans (mul_le_mul_of_nonneg_left hrad hcost)⟩

end
end Candidate.Feedback.FourthPower.MixedFirstInactiveConductor
