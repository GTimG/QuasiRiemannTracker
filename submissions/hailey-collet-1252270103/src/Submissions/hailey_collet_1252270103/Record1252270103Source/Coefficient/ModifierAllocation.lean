/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Exact common allocation with a retained tuple modifier. This is algebra and
positive-norm Cauchy, not a moment theorem for arbitrary modified coefficients.
It retains the particular squarefree, fixed-hole and Newton factors until
their proved restoration is invoked at the completed positive norm. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CoupledEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonProfile CenteredMomentSourceLiveAllocation CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
open CenteredMomentLiveSupport CenteredMomentLiveDomain CenteredMomentRemainingBox
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource CenteredMomentSourceRow
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def pulledModifier (B : Tuple ι) (modifier : Tuple ι→ℂ) (v : Tuple (liveIndices B)) : ℂ :=
  modifier (fun i=>B i*restoreTuple B v i)

def modifiedLiveProfile (modifier : Tuple ι→ℂ)
    (B : Tuple ι) (C R : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (v : Tuple (liveIndices B)) : ℂ :=
  pulledModifier B modifier v*liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v

theorem modified_residual_source_column (modifier : Tuple ι→ℂ)
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀i,B i≠0) (C R s a : Ideal O)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C) (hsC : s∣C)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∑u∈residualBoxes S C B hB,if finiteTupleProduct u=a then
      modifier (fun i=>B i*u i)*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
        (fun i=>B i*u i) else 0)=
      frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B hB)
          (modifiedLiveProfile modifier B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a := by
  have hh := residual_source_profile S hp B hB C R s hprod hsC ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
      (fun v=>pulledModifier B modifier v*(if finiteTupleProduct v=a then 1 else 0))
  rw [ite_eq_left (allocation_frozen_gate S hp C B hlabel)] at hh
  calc
    _ = ∑u∈residualBoxes S C B hB,
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i=>B i*u i)*
          (pulledModifier B modifier (remainingTuple B u)*
            (if finiteTupleProduct (remainingTuple B u)=a then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hf : ∀i,B (Sum.inl i)≠1 →u (Sum.inl i)=1 := by
        intro i hi
        have hui := hu
        simp only [residualBoxes,Fintype.mem_piFinset] at hui
        exact prime_residual_frozen B hB S hp i hi _ (Finset.mem_filter.mp (hui (Sum.inl i))).1
      rw [remaining_product B u hf]
      unfold pulledModifier
      rw [restore_remaining B u hf]
      split_ifs <;> ring
    _ = _ := hh.trans (by
      unfold frozenCoefficient finiteColumnCoefficient liveBox modifiedLiveProfile liveProfile
      rw [Finset.sum_filter]
      congr 1
      apply Finset.sum_congr
      · ext v
        simp only [Fintype.mem_piFinset]
      intro v hv
      split_ifs <;> ring)

theorem original_modified_source_column (modifier : Tuple ι→ℂ)
    (S : (ι⊕Fin 2)→Finset (Ideal O))
    (hS : ∀i,∀I∈S i,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (C R s a : Ideal O) (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a) (hsC : s∣C)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    finiteColumnCoefficient (Fintype.piFinset S)
      (fun v=>modifier v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v) (C*a)=
      ∑B : actualAllocations S C,frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
          (modifiedLiveProfile modifier B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a := by
  simp only [finiteColumnCoefficient,Finset.sum_filter]
  have halloc := original_coefficient_allocated S hS C a hC ha hCa
    (fun v=>modifier v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v)
  change (∑v∈Fintype.piFinset S,if finiteTupleProduct v=C*a then
    modifier v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v else 0)=_ at halloc
  rw [halloc]
  apply Finset.sum_congr rfl
  intro B hB
  have h := modified_residual_source_column modifier S hp B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R s a
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2 hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  simp only [finiteColumnCoefficient,Finset.sum_filter] at h
  convert h using 2
  rfl

theorem modifiedLiveProfile_original_support (modifier : Tuple ι→ℂ)
    (S : (ι⊕Fin 2)→Finset (Ideal O))
    (hS : ∀i,∀I∈S i,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀i,B i≠0) (C R a : Ideal O)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (hne : finiteColumnCoefficient (liveBox S B hB)
      (modifiedLiveProfile modifier B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a≠0) :
    C*a∈finiteColumns (Fintype.piFinset S) ∧ a≠0 ∧ IsCoprime C a := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hv,ha⟩ := Finset.mem_filter.mp hv
  have hnprofile : liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v≠0 :=
    (mul_ne_zero_iff.mp hvn).2
  have hm := CenteredMomentSourceCommonMask.profile_nonzero_masks (R*C)
    (fun i : liveIndices B=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v hnprofile
  rw [ha,IsCoprime.mul_right_iff] at hm
  have hsrc := restored_original_mem S hp C B hB hlabel v hv
  have he : finiteTupleProduct (fun i=>B i*restoreTuple B v i)=C*a := by
    rw [finiteTupleProduct,Finset.prod_mul_distrib]
    change finiteTupleProduct B*finiteTupleProduct (restoreTuple B v)=_
    rw [hprod,restore_product,ha]
  have hn : C*a≠0 := by
    rw [←he,finiteTupleProduct]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hS i _ (Fintype.mem_piFinset.mp hsrc i))
  exact ⟨Finset.mem_image.mpr ⟨_,hsrc,he⟩,right_ne_zero_of_mul hn,hm.1.2.symm⟩

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.original_modified_source_column
#print axioms OAI.SevenEighths.Record1252270103Source.modifiedLiveProfile_original_support
