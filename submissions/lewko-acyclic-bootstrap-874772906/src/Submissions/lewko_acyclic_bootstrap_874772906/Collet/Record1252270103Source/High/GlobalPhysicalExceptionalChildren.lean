/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The physical second block is paid by the actual retained modified children.
Only the genuine analytic bounds for those explicit children remain premises. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSelectedChildren
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103GlobalSelected
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Record1252270103Second
open Filter HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentFirstSectors
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondSectorColumns
open CenteredMomentSecondNonexceptional CenteredMomentSecondWholeKernel CenteredMomentSmooth
open CenteredMomentSecondSectorRetained CenteredMomentSecondWindowBudget
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization CenteredMomentOriginalCommonHarmonic
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "coefficient" => QRH.Record1252270103Source.High.CoupledFirst.coefficient
variable {ι : Type*} [Fintype ι]
local instance exceptionalChildrenDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Each analytic premise is a bound on an explicit child Input, with
pulledModifier, residual plain pools, original divisor mask, and the same
selected row predicate. Zero frozen coefficients need no child bound.
The complete allocation cardinality is kept in allocationBudget. -/
theorem actual_exceptional_physical_from_children
    (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃C0 : ℝ,0≤C0 ∧
      ∀K : ℝ,0<K → ∀n : Fin 4→ℤ,
      ∀(η : Character) (τ : RayCharacter→Character) (t : ℝ)
        (s : Input ι) (modifier : Tuple ι→ℂ) (R0 seed : Ideal O),
      s.W₁ 0=0 → s.W₂ 0=0 →
      let S := finiteColumns (Fintype.piFinset s.pools)
      let β := coefficient s modifier R0 seed
      ∀(C D : Ideal O) (hC : Supported C) (hD : Supported D),
      seed∣C → seed∣D → primeSupport C=primeSupport D →
      ∀U : Finset (CommonIndex C D),
      let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ : RayCharacter,∀I : Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) →
        ∀v : ℝ,heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*
          rayCharacter χ (primaryGenerator I)) →
      ∀(R : ℝ) (rows : Finset O) (Q : Ideal O) (m : O) (χ₀ : RayCharacter),
      Q≤Ideal.span {(72:O)} → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (CenteredMomentChildRows.childCharacter η χ₀) Q m A z) →
      ∀(Φ : 𝓢(ℝ,ℂ)) (H : ℝ),0<H →
      (∀z : O,0≤(Φ (normValue z/H)).re) → (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀(E₁ : Ideal O→actualAllocations s.pools C→ℝ) (E₂ : Ideal O→actualAllocations s.pools D→ℝ),
      (∀L b,0≤E₁ L b) → (∀L b,0≤E₂ L b) →
      (∀L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),
        Squarefree L →
        ∀χ : RayCharacter,∀v : ℝ,∀b : actualAllocations s.pools C,
        frozenCoefficient b C R0 s.ν s.W s.P≠0 →
          childDivisorEnergy s modifier C R0 L b (τ χ) v (fun z=>z≠0 ∧ CenteredExceptionalProfile.FixedInducingRow
            (CenteredMomentChildRows.childCharacter η χ) Q m A z) Φ H≤
            E₁ L b*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),
        Squarefree L →
        ∀χ : RayCharacter,∀v : ℝ,∀b : actualAllocations s.pools D,
        frozenCoefficient b D R0 s.ν s.W s.P≠0 →
          childDivisorEnergy s modifier D R0 L b (τ χ) v (fun z=>z≠0 ∧ CenteredExceptionalProfile.FixedInducingRow
            (CenteredMomentChildRows.childCharacter η χ) Q m A z) Φ H≤
            E₂ L b*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock η t S β C D hC hD U R rows W K n‖≤
        C0*(outerScalar C D K n*normalizer C D U)*
          (∑L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),
            ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
              (windowBudget J₁ t (allocationBudget s C R0 (E₁ L))*
               windowBudget J₂ t (allocationBudget s D R0 (E₂ L))))/
          (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay := by
  obtain ⟨C0,hC0,hkernel⟩ := actual_selected_physical_from_children (ι:=ι) W decay J₁ J₂
  refine ⟨C0,hC0,?_⟩
  intro K hK n η τ t s modifier R0 seed hz₁ hz₂ S β C D hC hD hsC hsD hCD U A hτ
    R rows Q m χ₀ hQ hmLam hm2 hrows hex Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  apply hkernel K hK n η τ t s modifier R0 seed hz₁ hz₂ C D hC hD hsC hsD hCD U hτ
    R rows (fun χ z=>z≠0 ∧ CenteredExceptionalProfile.FixedInducingRow
      (CenteredMomentChildRows.childCharacter η χ) Q m A z) hrows ?_ ?_
    Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  · intro χ z hz
    exact ⟨hrows z hz,(CenteredMomentSecondExceptionalKernel.exceptional_rows_pair
      η χ₀ χ χ Q hQ m A hmLam hm2 rows hex).1 z hz⟩
  · intro χ z hz
    have hpair:=CenteredMomentSecondExceptionalKernel.exceptional_rows_pair
      η χ₀ χ (χ⁻¹) Q hQ m A hmLam hm2 rows hex
    exact ⟨neg_ne_zero.mpr (hrows z hz),by simpa only [inv_inv] using hpair.2 z hz⟩

end
end OAI.SevenEighths.Record1252270103GlobalSelected
#print axioms OAI.SevenEighths.Record1252270103GlobalSelected.actual_exceptional_physical_from_children
