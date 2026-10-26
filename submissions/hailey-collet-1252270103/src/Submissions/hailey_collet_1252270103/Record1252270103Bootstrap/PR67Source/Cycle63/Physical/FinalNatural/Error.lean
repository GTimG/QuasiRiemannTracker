import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalErrorRadius
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.ExtractedBranches.Paid
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalNatural.State
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63FinalNatural
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRetainedWidth CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open Cycle63Moment.LowBranch Cycle63Physical.ExtractedBranches

theorem actual_error_retainedState_width
    (η₀ η₁ υ : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁) (hD₁ : Supported D₁)
    (heq : primeSupport C₁=primeSupport D₁) (E : Finset (CommonIndex C₁ D₁))
    (K₀ V Z a δ reserve ξ b J : ℝ) (N : ℕ) (p : O) (k : ℕ) (hp : p≠0)
    (hK₀ : 0<K₀) (hV : 0<V) (hZ : 1<Z) (hb : 0<b) (hJ : 0<J)
    (hmod : η₁.modulus=η₀.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun q : CommonIndex C₁ D₁ => q.val) E*activeConductor C₁ D₁})
    (hυ : (υ.modulus.absNorm:ℝ)≤J*(η₁.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (τ : RayFourExpansion.RayCharacter→ Character)
    (hf : Family υ C D hC hD U τ)
    (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ)
    (Bmask : ℝ) (χ : RayFourExpansion.RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask) :
    let c := Real.logb Z (C₁.absNorm:ℝ)
    let d := Real.logb Z (D₁.absNorm:ℝ)
    let k₀ := nominalLog C₁ D₁
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex C₁ D₁ => q.val) E}) K₀ V Z
    let Kerror := errorCommonRadius Z d k₀ c (3*a) δ reserve p k
    let R := frequencyRadius ((b^N*V/((C₁.absNorm:ℝ)*(normValue p)^k))^2/Kerror) Z ξ
    physicalBlock υ t S β C D hC hD U R rows W K n≠0 →
    (retainedState Z Bmask hZ (τ χ) Q P hP hPN R C D U).width≤
      (Real.logb Z K₀+Real.logb Z (η₀.modulus.absNorm:ℝ)-
        max (c-d+2*errorRemoval p Z k-errorMoving p Z k) 0-3*a-δ-reserve-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏q∈U,q.val).absNorm:ℝ))+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z J+Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  intro hne
  obtain ⟨z,hz⟩ := actual_retained_witness t S β _ rows W K n hne
  have hU : (∏q∈U,q.val)≠0 := Finset.prod_ne_zero_iff.mpr
    (fun q _ => (commonPrime_supported_ideal C D hC q).1)
  exact Cycle63FinalErrorRadius.actual_error_final_width η₀ η₁ υ (τ χ) C₁ D₁ hC₁ hD₁ heq E
    K₀ V Z a δ reserve ξ b J N p k hp hK₀ hV hZ hb hJ hmod hυ _ _ z _ hU
    (actual_family_conductor hf t S β _ rows W K hK n hne χ) hz

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end
end OAI.SevenEighths.Cycle63FinalNatural

end Record1252270103Bootstrap.PR67
