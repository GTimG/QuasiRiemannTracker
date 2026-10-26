/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modifier-preserving common allocation. Adapted from pinned OpenAI/Hailey Collet
LiveDomain and AmplificationLiveMask; support uses the actual modified tuple sum. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.ModifierEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationLiveMask CenteredMomentLiveDomain CenteredMomentRemainingBox
open CenteredMomentGaussEnergy CenteredMomentSourceAllocationEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentSecondHeightFamily CenteredMomentCommonPuncture CenteredMomentOriginalChildEnergy
open Record1252270103Source CenteredMomentFirstPhysicalSource
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance coupledFirstAllocationSupportDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem modified_live_column_sum (modifier:Tuple ι→ℂ) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (modifiedLiveProfile modifier B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    (∑ I∈supportedColumns (residualPool C hC.1 (finiteColumns (Fintype.piFinset S))),c I*f I)=
      ∑ I∈supportedColumns (finiteColumns (liveBox S B hB)),c I*f I := by
  dsimp only
  apply sum_same_support
  · intro I hI hn
    exact Finset.mem_filter.mpr ⟨finite_column_mem _ _ I hn,(Finset.mem_filter.mp hI).2⟩
  · intro I hI hn
    have hh := modifiedLiveProfile_original_support modifier S hS hp B hB C R I hlabel hprod
      ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hn
    exact Finset.mem_filter.mpr ⟨(mem_residualPool C hC.1 _ I).mpr hh.1,(Finset.mem_filter.mp hI).2⟩

theorem modified_live_gaussPolynomial (modifier:Tuple ι→ℂ) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (z : O) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (modifiedLiveProfile modifier B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => c I*f I) z=
      gaussPolynomial Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
        (fun I : supportedColumns T => c I*f I) z := by
  let c := finiteColumnCoefficient (liveBox S B hB)
    (modifiedLiveProfile modifier B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let T := finiteColumns (liveBox S B hB)
  change gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I : supportedColumns Q => c I*f I) z=_
  refine (source_gaussPolynomial Q (fun I => c I*f I) z).trans ?_
  refine Eq.trans ?_ (source_gaussPolynomial T (fun I => c I*f I) z).symm
  simpa only [mul_assoc] using modified_live_column_sum modifier S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ (fun I => f I*primaryGaussRow I z)

theorem modified_column_mask (modifier:Tuple ι→ℂ) (S : Finset (Tuple ι)) (R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s I : Ideal O) :
    finiteColumnCoefficient S
      (fun v=>modifier v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v) I=
      finiteColumnCoefficient S
        (fun v=>modifier v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1 v) I*
          (if s∣I then 1 else 0) := by
  unfold finiteColumnCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  dsimp only
  rw [profile_mask R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v,
    (Finset.mem_filter.mp hv).2,mul_assoc]

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.modified_live_gaussPolynomial
#print axioms QRH.Record1252270103Source.High.CoupledFirst.modified_column_mask
