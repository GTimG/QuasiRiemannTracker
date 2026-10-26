/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Common-allocation Cauchy for the literal retained tuple modifier. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.ModifierAllocation

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonProfile CenteredMomentSourceLiveAllocation CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
open CenteredMomentLiveDomain CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource
open CenteredMomentSourceRow CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem finite_source_allocation_energy {γ : Type*} [Fintype γ]
    (keep : O→Prop) (Q : Finset (Ideal O)) (c f : Ideal O→ℂ)
    (b : γ→ℂ) (T : γ→Finset (Ideal O)) (d : γ→Ideal O→ℂ)
    (hcolumn : ∀I : supportedColumns Q,c I=∑B,b B*d B I)
    (hQT : ∀B,∀I∈Q,d B I≠0 →I∈T B)
    (hTQ : ∀B,∀I∈T B,d B I≠0 →I∈Q)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    sourceRestrictedEnergy keep Q c f W K≤
      (Fintype.card γ:ℝ)*∑B,‖b B‖^2*sourceRestrictedEnergy keep (T B) (d B) f W K := by
  let d' := fun B (I : supportedColumns Q)=>d B I*f I
  have he (I : supportedColumns Q) : c I*f I=∑B,b B*d' B I := by
    rw [hcolumn I,Finset.sum_mul]
    simp only [d',mul_assoc]
  have hh := smoothed_restricted_allocation keep Finset.univ (sourceGenerator Q)
    (sourceGenerator_supported Q) b d' W K hK hW
  change restrictedEnergy keep Finset.univ (sourceGenerator Q) _ W K≤_
  rw [funext he]
  apply hh.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun x : ℝ=>‖b B‖^2*x)
  exact sourceRestrictedEnergy_same_support keep Q (T B) (d B) f W K (hQT B) (hTQ B)

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem original_modified_punctured_column (modifier : Tuple ι→ℂ)
    (S : (ι⊕Fin 2)→Finset (Ideal O))
    (hS : ∀i,∀I∈S i,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (C R s a : Ideal O) (hC : C≠0) (ha : a≠0) (hsC : s∣C)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (if IsCoprime C a then finiteColumnCoefficient (Fintype.piFinset S)
      (fun v=>modifier v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v) (C*a) else 0)=
      ∑B : actualAllocations S C,frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
          (modifiedLiveProfile modifier B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a := by
  by_cases hc : IsCoprime C a
  · rw [ite_eq_left hc]
    exact original_modified_source_column modifier S hS hp C R s a hC ha hc hsC
      ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  · rw [ite_eq_right hc]
    symm
    apply Finset.sum_eq_zero
    intro B hB
    have hz : finiteColumnCoefficient
        (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
        (modifiedLiveProfile modifier B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a=0 := by
      by_contra hn
      exact hc (modifiedLiveProfile_original_support modifier S hS hp B
        (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R a
        (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hn).2.2
    rw [hz,mul_zero]

/-- Actual modifier-preserving extraction, iterable for both row transforms.
No bound for an arbitrary modified moment is asserted. -/
theorem original_modified_restricted_energy (modifier : Tuple ι→ℂ)
    (S : (ι⊕Fin 2)→Finset (Ideal O))
    (hS : ∀i,∀I∈S i,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O→ℂ) (keep : O→Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I=>if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (fun v=>modifier v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v) (C*I) else 0) f W K≤
      ((actualAllocations S C).card:ℝ)*∑B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (modifiedLiveProfile modifier B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K := by
  rw [←Fintype.card_coe]
  apply finite_source_allocation_energy
  · intro I
    exact original_modified_punctured_column modifier S hS hp C R s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hsC ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  · intro B I hI hn
    exact finite_column_mem _ _ I hn
  · intro B I hI hn
    have hh := modifiedLiveProfile_original_support modifier S hS hp B
      (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R I
      (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
      ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hn
    exact (mem_residualPool C hC.1 _ I).mpr hh.1
  · exact hK
  · exact hW

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.finite_source_allocation_energy
#print axioms OAI.SevenEighths.Record1252270103Source.original_modified_restricted_energy
