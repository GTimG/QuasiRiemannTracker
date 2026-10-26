/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Actual positive row energies preserve the squarefree/corrected coefficient.
Only the original common-allocation Cauchy payment is used here. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CoupledProfile

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonProfile CenteredMomentSourceLiveAllocation CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
open CenteredMomentLiveDomain CenteredMomentRestrictedDomain CenteredMomentRestrictedEnergy
open CenteredMomentRestrictedSource CenteredMomentSourceRow CenteredMomentRowNorm CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem original_coupled_punctured_column (A₁ A₂ D : Ideal O) (F : Ideal O→ℂ)
    (S : (ι⊕Fin 2)→Finset (Ideal O))
    (hS : ∀i,∀I∈S i,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (C R s a : Ideal O) (hC : C≠0) (ha : a≠0) (hsC : s∣C)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (if IsCoprime C a then finiteColumnCoefficient (Fintype.piFinset S)
      (coupledProfile A₁ A₂ D F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*a) else 0)=
      ∑B : actualAllocations S C,frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
          (coupledLiveProfile A₁ A₂ D F B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a := by
  by_cases hc : IsCoprime C a
  · rw [ite_eq_left hc]
    exact original_coupled_source_column A₁ A₂ D F S hS hp C R s a hC ha hc hsC
      ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  · rw [ite_eq_right hc]
    symm
    apply Finset.sum_eq_zero
    intro B hB
    have hz : finiteColumnCoefficient
        (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
        (coupledLiveProfile A₁ A₂ D F B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a=0 := by
      by_contra hn
      exact hc (coupledLiveProfile_original_support A₁ A₂ D F S hS hp B
        (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R a
        (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hn).2.2
    rw [hz,mul_zero]

theorem sourceRestrictedEnergy_same_support (keep : O→Prop)
    (Q T : Finset (Ideal O)) (c f : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hQT : ∀I∈Q,c I≠0 →I∈T) (hTQ : ∀I∈T,c I≠0 →I∈Q) :
    sourceRestrictedEnergy keep Q c f W K=sourceRestrictedEnergy keep T c f W K := by
  unfold sourceRestrictedEnergy restrictedEnergy
  apply tsum_congr
  intro z
  apply congrArg (fun x : ℂ=>if keep z then ‖x‖^2*(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)
  rw [source_rowPolynomial Q (fun I=>c I*f I) z,source_rowPolynomial T (fun I=>c I*f I) z]
  simp only [mul_assoc]
  apply sum_same_support
  · intro I hI hn
    exact Finset.mem_filter.mpr ⟨hQT I (Finset.mem_filter.mp hI).1 hn,(Finset.mem_filter.mp hI).2⟩
  · intro I hI hn
    exact Finset.mem_filter.mpr ⟨hTQ I (Finset.mem_filter.mp hI).1 hn,(Finset.mem_filter.mp hI).2⟩

theorem coupled_live_restrictedEnergy (A₁ A₂ D : Ideal O) (F : Ideal O→ℂ)
    (S : (ι⊕Fin 2)→Finset (Ideal O))
    (hS : ∀i,∀I∈S i,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O→ℂ) (keep : O→Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (coupledLiveProfile A₁ A₂ D F B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S))) c f W K=
      sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB)) c f W K := by
  dsimp only
  apply sourceRestrictedEnergy_same_support
  · intro I hI hn
    exact finite_column_mem _ _ I hn
  · intro I hI hn
    have hh := coupledLiveProfile_original_support A₁ A₂ D F S hS hp B hB C R I hlabel hprod
      ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hn
    exact (mem_residualPool C hC.1 _ I).mpr hh.1

/-- Exact source-preserving common extraction for the coupled coefficient.
It can be iterated: the child is the same coupled profile with accumulated
ordinary ideals, frozen column and puncture, before any divisor expansion. -/
theorem original_coupled_restricted_energy (A₁ A₂ D : Ideal O) (F : Ideal O→ℂ)
    (S : (ι⊕Fin 2)→Finset (Ideal O))
    (hS : ∀i,∀I∈S i,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O→ℂ) (keep : O→Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I=>if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (coupledProfile A₁ A₂ D F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K≤
      ((actualAllocations S C).card:ℝ)*∑B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (coupledLiveProfile A₁ A₂ D F B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K := by
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let b := fun B : actualAllocations S C=>frozenCoefficient B C R ν Wslot P
  let d := fun (B : actualAllocations S C) (I : supportedColumns Q)=>
    finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
      (coupledLiveProfile A₁ A₂ D F B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I*f I
  have he (I : supportedColumns Q) :
      (if IsCoprime C (I:Ideal O) then finiteColumnCoefficient (Fintype.piFinset S)
        (coupledProfile A₁ A₂ D F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)*f I=
      ∑B,b B*d B I := by
    rw [original_coupled_punctured_column A₁ A₂ D F S hS hp C R s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hsC ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂,Finset.sum_mul]
    simp only [b,d,mul_assoc]
  have hh := smoothed_restricted_allocation keep Finset.univ (sourceGenerator Q)
    (sourceGenerator_supported Q) b d W K hK hW
  change restrictedEnergy keep Finset.univ (sourceGenerator Q) _ W K≤_
  rw [funext he]
  apply hh.trans_eq
  rw [Fintype.card_coe]
  apply congrArg (fun x : ℝ=>((actualAllocations S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  simpa only [b,d,sourceRestrictedEnergy] using
    congrArg (fun x : ℝ=>‖frozenCoefficient B C R ν Wslot P‖^2*x)
      (coupled_live_restrictedEnergy A₁ A₂ D F S hS hp B
        (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R hC
        (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f keep W K)

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.sourceRestrictedEnergy_same_support
#print axioms OAI.SevenEighths.Record1252270103Source.original_coupled_restricted_energy
