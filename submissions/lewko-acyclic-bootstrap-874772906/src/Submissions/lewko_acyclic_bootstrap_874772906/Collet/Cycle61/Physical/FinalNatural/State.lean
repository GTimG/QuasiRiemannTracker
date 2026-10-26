import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.FinalRadius
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.LowBranch.DaughterState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonExceptionalGates

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61FinalNatural
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss ActualEisensteinCubic
open CenteredMomentEnergyState CenteredMomentEnergyChildState
open CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRetainedWidth CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondLiveBlock
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRadicalBudget CenteredMomentFixedRowMask CenteredExceptionalProfile
open Cycle61Moment.LowBranch
local notation "O" => HeckeFamily.O

def retainedScale (R : ℝ) (C D : Ideal O) (U : Finset (CommonIndex C D)) : ℝ :=
  max 1 (4*R/(normValue (commonFrequencyGenerator C D)*
    normValue (nonunitFrequencyGenerator C D U)))

def retainedState (Z Bmask : ℝ) (hZ : 1<Z) (τ : Character) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask)
    (R : ℝ) (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    NaturalState Z Bmask 2 :=
  daughterState τ Q P ballProfile Z (retainedScale R C D U) Bmask 2
    hZ (le_max_left _ _) hP hPN ball_support ballProfile_nonneg

theorem retainedState_width (Z Bmask : ℝ) (hZ : 1<Z) (τ : Character) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask)
    (R : ℝ) (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    (retainedState Z Bmask hZ τ Q P hP hPN R C D U).width =
      Real.logb Z (retainedScale R C D U)+Real.logb Z (τ.modulus.absNorm:ℝ) := rfl

theorem retainedState_keep (Z Bmask : ℝ) (hZ : 1<Z) (τ : Character) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask)
    (R : ℝ) (C D : Ideal O) (U : Finset (CommonIndex C D)) (z : O) :
    (retainedState Z Bmask hZ τ Q P hP hPN R C D U).radial.keep z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  change (z≠0 ∧ ¬FixedInducingRow τ Q (fixedBadMask*idealGenerator P) 1 z) ↔ _
  by_cases hz : z=0
  · simp [hz]
  · rw [fixedInducingRow_mul_mask_iff τ Q fixedBadMask (idealGenerator P) 1 z
      fixedBadMask_ne_zero (idealGenerator_ne_zero P hP) one_ne_zero hz
      (dvd_mul_right _ _) (dvd_mul_left _ _)]

theorem actual_source_puncture {α : Type*} [Fintype α] [DecidableEq α]
    (s : CenteredMomentCommonRadialData.Input α) (C P : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (Z Bmask Bsource : ℝ) (hZ : 0<Z) (hP : P≠0)
    (hPN : (P.absNorm:ℝ)≤Z^Bmask) (hCN : (C.absNorm:ℝ)≤Z^Bsource) :
    P*C≠0 ∧ ((P*C).absNorm:ℝ)≤Z^(Bmask+Bsource) :=
  ⟨mul_ne_zero hP (CenteredMomentAllocatedNaturalRadial.common_nonzero s C B),
    common_puncture_bound Z Bmask Bsource hZ P C hPN hCN⟩

theorem actual_partRows_majorized (Z Bmask : ℝ) (hZ : 1<Z) (τ : Character)
    (Q P : Ideal O) (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask)
    (η : Character) (χ : RayFourExpansion.RayCharacter) (m : O)
    (R : ℝ) (C D : Ideal O) (U : Finset (CommonIndex C D)) (z : O)
    (hz : z∈CenteredMomentSecondEnergySplit.partRows false η χ Q m C D U R) :
    1≤((retainedState Z Bmask hZ τ Q P hP hPN R C D U).radial.profile
      (normValue z/(retainedState Z Bmask hZ τ Q P hP hPN R C D U).radial.scale)).re := by
  have hs : z∈CenteredMomentSecondEnergySplit.sourceRows C D U R :=
    (Finset.mem_filter.mp hz).1
  have hw := liveRows_weight C D U R _ z hs
  exact Cycle61FinalRadius.actual_retained_majorant R _ _ z hw

section Actual
variable {η : Character} {C D : Ideal O} {hC : Supported C} {hD : Supported D}
  {U : Finset (CommonIndex C D)} {τ : RayFourExpansion.RayCharacter→Character}
  (hf : Family η C D hC hD U τ)
  (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ) (R : ℝ) (rows : Finset O)
  (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ)
  (hne : physicalBlock η t S β C D hC hD U R rows W K n≠0)

include hf hK hne in
theorem actual_family_conductor (χ : RayFourExpansion.RayCharacter) :
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
      (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm :=
  (hf.physical_budget t S β R rows W K hK n hne χ).1

include hne in
theorem actual_retained_witness : ∃z : O,
    retainedWeight R (normValue ((commonFrequencyGenerator C D*
      nonunitFrequencyGenerator C D U)*z))≠0 := by
  obtain ⟨z,hz,_,_,_⟩ := physicalBlock_live_dyadic_witness η t S β C D hC hD U
    R rows W K n hne
  exact ⟨z,liveRows_weight C D U R rows z hz⟩

include hf hK hne in
theorem actual_retainedState_width (Z Bmask : ℝ) (hZ : 1<Z)
    (χ : RayFourExpansion.RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask) :
    (retainedState Z Bmask hZ (τ χ) Q P hP hPN R C D U).width≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏p∈U,p.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨z,hz⟩ := actual_retained_witness t S β R rows W K n hne
  have hU : (∏p∈U,p.val)≠0 := Finset.prod_ne_zero_iff.mpr
    (fun p _ => (commonPrime_supported_ideal C D hC p).1)
  exact retained_log_budget η (τ χ) _ _ z _ hU
    (actual_family_conductor hf t S β R rows W K hK n hne χ) R Z hZ hz

include hf in
theorem actual_nonexceptional_keep (Z Bmask : ℝ) (hZ : 1<Z)
    (χ : RayFourExpansion.RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask)
    (m z : O) (hm : m≠0) (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m) :
    CenteredMomentRestrictedEnergy.nonexceptional η χ Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      (retainedState Z Bmask hZ (τ χ) Q P hP hPN R C D U).radial.keep z := by
  rw [retainedState_keep]
  exact hf.nonexceptional_iff χ Q m z hm hml hm2

include hf in
theorem actual_sourceRadial_eq (Z Bmask : ℝ) (hZ : 1<Z)
    (χ : RayFourExpansion.RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask)
    (m : O) (hm : m≠0) (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m) :
    CenteredMomentSecondOriginalChildren.sourceRadial
      (CenteredMomentRestrictedEnergy.nonexceptional η χ Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))
      ballProfile (retainedScale R C D U) (zero_lt_one.trans_le (le_max_left _ _))
      (fun _ => ballProfile_nonneg _) =
      (retainedState Z Bmask hZ (τ χ) Q P hP hPN R C D U).radial := by
  have he : CenteredMomentRestrictedEnergy.nonexceptional η χ Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) =
      daughterKeep (τ χ) Q P := by
    funext z
    exact propext (actual_nonexceptional_keep hf R Z Bmask hZ χ Q P hP hPN m z hm hml hm2)
  unfold CenteredMomentSecondOriginalChildren.sourceRadial retainedState daughterState
  rw [he]

end Actual

theorem actual_main_retainedState_width
    (η₀ η₁ : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁) (hD₁ : Supported D₁)
    (heq : primeSupport C₁=primeSupport D₁) (E : Finset (CommonIndex C₁ D₁))
    (K₀ V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK₀ : 0<K₀) (hV : 0<V) (hZ : 1<Z) (hb : 0<b)
    (hmod : η₁.modulus=η₀.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun p : CommonIndex C₁ D₁ => p.val) E*
        activeConductor C₁ D₁})
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (τ : RayFourExpansion.RayCharacter→Character)
    (hf : Family η₁ C D hC hD U τ)
    (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ)
    (Bmask : ℝ) (χ : RayFourExpansion.RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤Z^Bmask) :
    let c := Real.logb Z (C₁.absNorm:ℝ)
    let d := Real.logb Z (D₁.absNorm:ℝ)
    let k := nominalLog C₁ D₁
      (Ideal.span {primeSubsetGenerator (fun p : CommonIndex C₁ D₁ => p.val) E}) K₀ V Z
    let Kmain := CenteredMomentAmplifiedRetainedRadius.mainCommonRadius Z d k c (3*a) δ reserve
    let R := frequencyRadius ((b^N*V/(C₁.absNorm:ℝ))^2/Kmain) Z ξ
    physicalBlock η₁ t S β C D hC hD U R rows W K n≠0 →
    (retainedState Z Bmask hZ (τ χ) Q P hP hPN R C D U).width≤
      (Real.logb Z K₀+Real.logb Z (η₀.modulus.absNorm:ℝ)-max (c-d) 0-6*a-δ-reserve-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏p∈U,p.val).absNorm:ℝ))+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  intro hne
  obtain ⟨z,hz⟩ := actual_retained_witness t S β _ rows W K n hne
  have hU : (∏p∈U,p.val)≠0 := Finset.prod_ne_zero_iff.mpr
    (fun p _ => (commonPrime_supported_ideal C D hC p).1)
  exact Cycle61FinalRadius.actual_main_final_width η₀ η₁ (τ χ) C₁ D₁ hC₁ hD₁ heq E
    K₀ V Z a δ reserve ξ b N hK₀ hV hZ hb hmod _ _ z _ hU
    (actual_family_conductor hf t S β _ rows W K hK n hne χ) hz
end
end OAI.SevenEighths.Cycle61FinalNatural
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_retainedState_width
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_nonexceptional_keep
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_main_retainedState_width
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_sourceRadial_eq
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_partRows_majorized
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_source_puncture
