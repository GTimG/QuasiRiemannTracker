import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalRadius
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.DaughterState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonExceptionalGates
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63FinalNatural
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss ActualEisensteinCubic
open CenteredMomentEnergyState CenteredMomentEnergyChildState
open CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRetainedWidth CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondLiveBlock
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRadicalBudget CenteredMomentFixedRowMask CenteredExceptionalProfile
open Cycle63Moment.LowBranch

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
  exact Cycle63FinalRadius.actual_retained_majorant R _ _ z hw

section Actual
variable {η : Character} {C D : Ideal O} {hC : Supported C} {hD : Supported D}
  {U : Finset (CommonIndex C D)} {τ : RayFourExpansion.RayCharacter→ Character}
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

end Actual

end
end OAI.SevenEighths.Cycle63FinalNatural

end Record1252270103Bootstrap.PR67
