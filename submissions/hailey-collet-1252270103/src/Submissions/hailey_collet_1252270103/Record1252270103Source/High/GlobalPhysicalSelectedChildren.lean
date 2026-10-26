/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The physical second block is paid by the actual retained modified children.
Only the genuine analytic bounds for those explicit children remain premises. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.CoupledBudget
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSelectedSquarefree

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
local instance selectedChildrenDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Each analytic premise is a bound on an explicit child Input, with
pulledModifier, residual plain pools, original divisor mask, and the same
selected row predicate. Zero frozen coefficients need no child bound.
The complete allocation cardinality is kept in allocationBudget. -/
theorem actual_selected_physical_from_children
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
      ∀(R : ℝ) (rows : Finset O) (keep : RayCharacter→O→Prop),
      (∀z∈rows,z≠0) →
      (∀χ : RayCharacter,∀z∈rows,keep χ z) →
      (∀χ : RayCharacter,∀z∈rows,keep χ (-z)) →
      ∀(Φ : 𝓢(ℝ,ℂ)) (H : ℝ),0<H →
      (∀z : O,0≤(Φ (normValue z/H)).re) → (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀(E₁ : Ideal O→actualAllocations s.pools C→ℝ) (E₂ : Ideal O→actualAllocations s.pools D→ℝ),
      (∀L b,0≤E₁ L b) → (∀L b,0≤E₂ L b) →
      (∀L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),
        Squarefree L →
        ∀χ : RayCharacter,∀v : ℝ,∀b : actualAllocations s.pools C,
        frozenCoefficient b C R0 s.ν s.W s.P≠0 →
          childDivisorEnergy s modifier C R0 L b (τ χ) v (keep χ) Φ H≤
            E₁ L b*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),
        Squarefree L →
        ∀χ : RayCharacter,∀v : ℝ,∀b : actualAllocations s.pools D,
        frozenCoefficient b D R0 s.ν s.W s.P≠0 →
          childDivisorEnergy s modifier D R0 L b (τ χ) v (keep χ) Φ H≤
            E₂ L b*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock η t S β C D hC hD U R rows W K n‖≤
        C0*(outerScalar C D K n*normalizer C D U)*
          (∑L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),
            ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
              (windowBudget J₁ t (allocationBudget s C R0 (E₁ L))*
               windowBudget J₂ t (allocationBudget s D R0 (E₂ L))))/
          (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay := by
  obtain ⟨C0,hC0,hkernel⟩ := actual_selected_block_from_squarefree_source W decay J₁ J₂
  refine ⟨C0,hC0,?_⟩
  intro K hK n η τ t s modifier R0 seed hz₁ hz₂ S β C D hC hD hsC hsD hCD U A hτ
    R rows keep hrows hkeep₁ hkeep₂ Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  let r := dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hr : 0<r := div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  have hh := hkernel r hr η τ t S β C D hC hD hCD U hτ R rows
    (fun _=>Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1)))
    (dyadicScale (n 2)) (dyadicScale (n 3)) (dyadicScale_pos _) (dyadicScale_pos _)
    keep hkeep₁ hkeep₂ Φ H hH hΦ hmajor
    (fun L=>allocationBudget s C R0 (E₁ L)) (fun L=>allocationBudget s D R0 (E₂ L))
    (fun L=>allocationBudget_nonneg s C R0 (E₁ L) (hE₁ L))
    (fun L=>allocationBudget_nonneg s D R0 (E₂ L) (hE₂ L))
    (by
      intro L hL hsf χ v
      exact (actual_allocated_divisor_energy s modifier C R0 seed L hC hsC
        (τ χ) v (keep χ) Φ H hH
        (by simpa only [normValue_eq_embedding] using hΦ)).trans
          (allocatedDivisorEnergy_le s modifier C R0 L (τ χ) v
            (keep χ) Φ H ((1+‖v‖)^(2*J₁)) (E₁ L) (hleft L hL hsf χ v)))
    (by
      intro L hL hsf χ v
      exact (actual_allocated_divisor_energy s modifier D R0 seed L hD hsD
        (τ χ) v (keep χ) Φ H hH
        (by simpa only [normValue_eq_embedding] using hΦ)).trans
          (allocatedDivisorEnergy_le s modifier D R0 L (τ χ) v
            (keep χ) Φ H ((1+‖v‖)^(2*J₂)) (E₂ L) (hright L hL hsf χ v)))
  change (1+r)^decay*‖normalizedBlock η t S β C D hC hD U R rows W K n‖≤_ at hh
  have ho : 0≤outerScalar C D K n := by unfold outerScalar; positivity
  have hn : 0≤normalizer C D U := (normalizer_pos C D hC U).le
  have hp : 0<(1+r)^decay := pow_pos (by linarith) _
  have hphys : ‖physicalBlock η t S β C D hC hD U R rows W K n‖=
      outerScalar C D K n*normalizer C D U*‖normalizedBlock η t S β C D hC hD U R rows W K n‖ := by
    rw [physicalBlock_eq η t S β C D hC hD U R rows hrows W K hK n,
      norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]
  rw [hphys]
  apply (le_div_iff₀ hp).mpr
  have hmul := mul_le_mul_of_nonneg_left hh (mul_nonneg ho hn)
  convert hmul using 1 <;> ring

end
end OAI.SevenEighths.Record1252270103GlobalSelected

#print axioms OAI.SevenEighths.Record1252270103GlobalSelected.actual_selected_physical_from_children
