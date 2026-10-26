/- Copyright (c) 2026 Sil. Apache-2.0.
Complete common extraction in the positive Gauss energy, retaining the
literal restriction on each live tuple. Domain completion is justified
by coefficient support, never by deleting a mask inside a square.
-/
import Candidate.FourthPower.MixedCommonCoefficient
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalChildEnergy

set_option autoImplicit false
namespace Candidate.FourthPower.MixedCommonEnergy
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceLiveAllocation CenteredMomentSourceLiveColumn
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentSourceCommonMask
open CenteredMomentLiveSupport CenteredMomentLiveDomain CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentSourceSmoothedAllocation
open MixedCommonAllocation MixedCommonCoefficient
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Any extra tuple multiplier preserves support; this is only a support
identity and does not assert a moment bound for arbitrary multipliers. -/
theorem masked_live_support (S : (ι⊕Fin 2)→Finset Id)
    (hS : ∀j,∀I∈S j,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀j,B j≠0) (C R a : Id)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id)
    (θ : Tuple (liveIndices B)→ℂ)
    (hne : finiteColumnCoefficient (liveBox S B hB)
      (fun v=>θ v*liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v) a≠0) :
    C*a∈finiteColumns (Fintype.piFinset S) ∧ a≠0 ∧ IsCoprime C a := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hv,ha⟩ := Finset.mem_filter.mp hv
  have hm := profile_nonzero_masks (R*C) (fun i : liveIndices B=>ν i.val)
    (fun i=>Wslot i.val) (fun i=>P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v (mul_ne_zero_iff.mp hvn).2
  rw [ha,IsCoprime.mul_right_iff] at hm
  have hsrc := restored_original_mem S hp C B hB hlabel v hv
  have he : finiteTupleProduct (fun j=>B j*CenteredMomentRemainingBox.restoreTuple B v j)=C*a := by
    rw [finiteTupleProduct,Finset.prod_mul_distrib]
    change finiteTupleProduct B*finiteTupleProduct (CenteredMomentRemainingBox.restoreTuple B v)=_
    rw [hprod,restore_product,ha]
  have hn : C*a≠0 := by
    rw [←he,finiteTupleProduct]
    exact Finset.prod_ne_zero_iff.mpr (fun j _=>hS j _ (Fintype.mem_piFinset.mp hsrc j))
  exact ⟨Finset.mem_image.mpr ⟨_,hsrc,he⟩,right_ne_zero_of_mul hn,hm.1.2.symm⟩

theorem punctured_restricted_column (H : Id) (S : (ι⊕Fin 2)→Finset Id)
    (hS : ∀j,∀I∈S j,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (C R s a : Id) (hC : C≠0) (ha : a≠0) (hsC : s∣C)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id) :
    (if IsCoprime C a then finiteColumnCoefficient (Fintype.piFinset S)
      (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v) (C*a)
      else 0)=
      ∑B : actualAllocations S C,
        (frozenWeight H B.val*frozenCoefficient B.val C R ν Wslot P)*
          finiteColumnCoefficient
            (liveBox S B.val (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).1)
            (fun v=>tupleWeight H v*liveProfile B.val C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v) a := by
  by_cases hc : IsCoprime C a
  · rw [ite_eq_left hc]
    exact original_restricted_column H S hS hp C R s a hC ha hc hsC ν Wslot P
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  · rw [ite_eq_right hc]
    symm
    apply Finset.sum_eq_zero
    intro B hB
    have hz : finiteColumnCoefficient
        (liveBox S B.val (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).1)
        (fun v=>tupleWeight H v*liveProfile B.val C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v) a=0 := by
      by_contra hn
      exact hc (masked_live_support S hS hp B.val
        (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).1 C R a
        (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (tupleWeight H) hn).2.2
    rw [hz,mul_zero]

theorem source_energy_congr (S T : Finset Id) (c f : Id→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ)
    (h : ∀I,c I≠0→(I∈S↔I∈T)) :
    sourceGaussEnergy S c f W K=sourceGaussEnergy T c f W K := by
  have he (z : O) : gaussPolynomial Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S=>c I*f I) z=
      gaussPolynomial Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
        (fun I : supportedColumns T=>c I*f I) z := by
    rw [source_gaussPolynomial S (fun I => c I*f I) z,
      source_gaussPolynomial T (fun I => c I*f I) z]
    simpa only [mul_assoc] using sum_same_support (supportedColumns S) (supportedColumns T)
      c (fun I=>f I*primaryGaussRow I z)
      (fun I hI hn=>Finset.mem_filter.mpr ⟨(h I hn).mp (Finset.mem_filter.mp hI).1,
        (Finset.mem_filter.mp hI).2⟩)
      (fun I hI hn=>Finset.mem_filter.mpr ⟨(h I hn).mpr (Finset.mem_filter.mp hI).1,
        (Finset.mem_filter.mp hI).2⟩)
  unfold sourceGaussEnergy gaussEnergy
  apply tsum_congr
  intro z
  rw [he]

theorem frozen_scalar_norm_le (H : Id) (B : Tuple ι) (c : ℂ) :
    ‖frozenWeight H B*c‖≤‖c‖ := by
  unfold frozenWeight
  split_ifs <;> simp [norm_nonneg]

/-- The actual positive Gauss energy decomposes into the original live
profiles with the exact restricted tuple mask still present. -/
theorem restricted_child_energy (H : Id) (S : (ι⊕Fin 2)→Finset Id)
    (hS : ∀j,∀I∈S j,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (C R s : Id) (hC : Supported C) (hsC : s∣C)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id)
    (f : Id→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceGaussEnergy (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I=>if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v) (C*I)
        else 0) f W K).re ≤
      ((actualAllocations S C).card:ℝ)*∑B : actualAllocations S C,
        ‖frozenWeight H B.val*frozenCoefficient B.val C R ν Wslot P‖^2*
          (sourceGaussEnergy
            (finiteColumns (liveBox S B.val (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B.val (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).1)
              (fun v=>tupleWeight H v*liveProfile B.val C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v)) f W K).re := by
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let b := fun B : actualAllocations S C=>frozenWeight H B.val*frozenCoefficient B.val C R ν Wslot P
  let c := fun (B : actualAllocations S C)=>finiteColumnCoefficient
    (liveBox S B.val (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).1)
    (fun v=>tupleWeight H v*liveProfile B.val C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v)
  let d := fun (B : actualAllocations S C)(I : supportedColumns Q)=>c B I*f I
  have he (I : supportedColumns Q) :
      (if IsCoprime C (I:Id) then finiteColumnCoefficient (Fintype.piFinset S)
        (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v) (C*I)
        else 0)*f I=∑B,b B*d B I := by
    rw [punctured_restricted_column H S hS hp C R s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hsC ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂,Finset.sum_mul]
    simp only [b,c,d,mul_assoc]
  have hh := smoothed_allocation_energy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    b d W K hK hW
  change (gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) _ W K).re≤_
  rw [funext he]
  apply hh.trans_eq
  rw [Fintype.card_coe]
  apply congrArg (fun x : ℝ=>((actualAllocations S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  have hsame := source_energy_congr Q
    (finiteColumns (liveBox S B.val (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).1))
    (c B) f W K (by
      intro I hn
      constructor
      · intro _
        exact finite_column_mem _ _ I hn
      · intro _
        exact (mem_residualPool C hC.1 _ I).mpr (masked_live_support S hS hp B.val
          (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).1 C R I
          (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
          ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (tupleWeight H) hn).1)
  simpa only [sourceGaussEnergy,b,c,d] using
    congrArg (fun x : ℂ=>‖b B‖^2*x.re) hsame

end
end Candidate.FourthPower.MixedCommonEnergy
