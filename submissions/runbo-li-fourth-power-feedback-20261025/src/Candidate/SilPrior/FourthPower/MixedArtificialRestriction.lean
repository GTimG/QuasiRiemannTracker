/- Copyright (c) 2026 Sil. Apache-2.0.
Exact artificial-projector expansion on the actual restricted tuple.
Freeze every power on the fixed support, keep its allocation sign,
and leave the standard restricted live profile punctured at that support.
-/
import Candidate.SilPrior.FourthPower.MixedFixedSupport

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.MixedArtificialRestriction
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox CenteredMomentCommonPrimeSlots
open CenteredMomentSourceLiveAllocation CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass
open CenteredMomentCommonPuncture CenteredMomentRemainingBox CenteredMomentFirstSectors
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open MixedCommonRestriction MixedCommonAllocation MixedCommonCoefficient MixedFixedSupport
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem restricted_tuple_fifth_free (H : Id) (v : Tuple ι)
    (hv : ∀j,v j≠0) (hp : ∀i,Prime (v (Sum.inl i))) (hr : tupleRestriction H v) :
    SexticSieve.PowerFree 5 (finiteTupleProduct v) := by
  let p : ι→PrimeIdeal := fun i=>⟨v (Sum.inl i),hp i⟩
  have hh := KernelWholeColumns.restricted_whole_fifth_free p
    (fun i j he=>hr.2 (congrArg Subtype.val he)) (hv (Sum.inr 0)) (hv (Sum.inr 1)) hr.1.1
    (by
      intro i
      apply (prime_coprime (p i) _).mp
      exact (IsCoprime.mul_left_iff.mp hr.1.2).2.of_isCoprime_of_dvd_left
        (Finset.dvd_prod_of_mem (fun i=>v (Sum.inl i)) (Finset.mem_univ i)))
  have he : finiteTupleProduct v=
      v (Sum.inr 0)*v (Sum.inr 1)*KernelWholeColumns.markedProduct p := by
    simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,
      KernelWholeColumns.markedProduct,p]
    ring
  rwa [he]

theorem fixed_weight_split (H : Id) (S : (ι⊕Fin 2)→Finset Id)
    (hS : ∀j,∀I∈S j,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (F : Id) (hF : F≠0) (B : boundedLabels S F) (u : Tuple ι)
    (hu : u∈residualBoxes S F B.val
      (allocation_data S F B.val (Finset.mem_filter.mp B.property).1).1) :
    tupleWeight H (fun j=>B.val j*u j)=
      frozenWeight H B.val*tupleWeight H (remainingTuple B.val u) := by
  have hB := allocation_data S F B.val (Finset.mem_filter.mp B.property).1
  have hc (j) : IsCoprime F (u j) := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hu j)).2
  have hprod (j) : IsCoprime (finiteTupleProduct B.val) (u j) := by
    apply IsCoprime.prod_left
    intro k hk
    have hpow : IsCoprime (F^4) (u j) := (hc j).pow_left
    exact hpow.of_isCoprime_of_dvd_left ((Finset.mem_filter.mp B.property).2 k)
  have he := tuple_restriction_split H (finiteTupleProduct B.val) B.val u hB.1
    (fun j=>right_ne_zero_of_mul (hS j _ (residual_original_mem S F B.val hB.1 u hu j))) rfl
    (actual_frozen_slots S hS F hF B.val hB.1 hB.2 u hu hp)
    (fun i=>hp i _ (residual_original_mem S F B.val hB.1 u hu (Sum.inl i))) hprod
  unfold tupleWeight frozenWeight
  rw [he]
  split_ifs <;> simp_all

/-- Baseline's source-profile reindexing with the puncture F separated
from the product of extracted factors. Its finite proof is unchanged
apart from that separation; all frozen coefficient and profile factors remain. -/
theorem residual_profile_at_support (S : (ι⊕Fin 2)→Finset Id)
    (hp : ∀i,∀I∈S (Sum.inl i),Prime I) (F R : Id)
    (B : Tuple ι) (hB : ∀j,B j≠0) (hlabel : B∈allocationLabels S F)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id)
    (g : Tuple (liveIndices B)→ℂ) :
    (∑u∈residualBoxes S F B hB,
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1 (fun j=>B j*u j)*
        g (remainingTuple B u))=
      frozenCoefficient B (finiteTupleProduct B) R ν Wslot P*
        ∑v∈liveBox S B hB,liveProfile B F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v*g v := by
  let T := fun j=>residualPool (B j) (hB j) (S j)
  let A := frozenCoefficient B (finiteTupleProduct B) R ν Wslot P
  let G := fun v : Tuple (liveIndices B)=>liveProfile B F R ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v*g v
  have hf := prime_residual_frozen B hB S hp
  rw [residualBoxes_sum]
  calc
    _ = ∑u∈Fintype.piFinset T,A*G (remainingTuple B u) := by
      apply Finset.sum_congr
      · ext u;simp only [Fintype.mem_piFinset];rfl
      · intro u hu
        have hfu : ∀i,B (Sum.inl i)≠1→u (Sum.inl i)=1 :=
          fun i hi=>hf i hi _ (Fintype.mem_piFinset.mp hu _)
        rw [profile_common_allocation B u (finiteTupleProduct B) R 1 rfl (one_dvd _) hfu]
        change (if IsCoprime F (finiteTupleProduct u) then 1 else 0)*(A*_*g (remainingTuple B u))=_
        rw [remaining_product B u hfu]
        dsimp only [G,liveProfile]
        rw [←profileCoefficient_puncture F R]
        ring
    _ = A*(∑u∈Fintype.piFinset T,G (remainingTuple B u)) := by rw [Finset.mul_sum]
    _ = _ := by
      have he := remaining_box_sum_gate B T hf (fun u=>G (remainingTuple B u))
      simp only [remaining_restore,T,mem_residualPool,mul_one] at he
      rw [ite_eq_left (allocation_frozen_gate S hp F B hlabel)] at he
      apply congrArg (fun x : ℂ=>A*x)
      refine Eq.trans ?_ (Eq.trans he ?_)
      · apply Finset.sum_congr
        · ext u;simp only [Fintype.mem_piFinset,T]
        · intro u hu;rfl
      · apply Finset.sum_congr
        · ext v;simp only [liveBox,Fintype.mem_piFinset]
        · intro v hv;rfl

/-- The literal artificial allocation, including its sign, restricted
ordinary pair and marked labels, is a finite sum of standard punctured
live profiles. This identity supplies no unproved energy hypothesis. -/
theorem allocated_restricted_character_sum (H : Id) (S : (ι⊕Fin 2)→Finset Id)
    (hS : ∀j,∀I∈S j,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (D F R : Id) (hF : F≠0) (hDF : D∣F)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (ψ : Id→*ℂ)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id) :
    (∑v∈Fintype.piFinset S,tupleWeight H v*allocationTerm D Finset.univ v a*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1 v*ψ (finiteTupleProduct v))=
      ∑B : boundedLabels S F,
        (frozenWeight H B.val*allocationTerm D Finset.univ B.val a*
          frozenCoefficient B.val (finiteTupleProduct B.val) R ν Wslot P*ψ (finiteTupleProduct B.val))*
        ∑v∈liveBox S B.val (allocation_data S F B.val (Finset.mem_filter.mp B.property).1).1,
          tupleWeight H v*liveProfile B.val F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v*
            ψ (finiteTupleProduct v) := by
  let c := fun v : Tuple ι=>tupleWeight H v*allocationTerm D Finset.univ v a*
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1 v*ψ (finiteTupleProduct v)
  have hc (v) (hv : v∈Fintype.piFinset S) (hn : c v≠0) :
      SexticSieve.PowerFree 5 (finiteTupleProduct v) := by
    have hw : tupleWeight H v≠0 :=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1).1
    have hr : tupleRestriction H v := by
      by_contra hh
      exact hw (by simp only [tupleWeight,ite_eq_right hh])
    exact restricted_tuple_fifth_free H v (fun j=>hS j _ (Fintype.mem_piFinset.mp hv j))
      (fun i=>hp i _ (Fintype.mem_piFinset.mp hv (Sum.inl i))) hr
  rw [bounded_residual_sum S hS F hF c hc]
  apply Finset.sum_congr rfl
  intro B hB
  let hb := (allocation_data S F B.val (Finset.mem_filter.mp B.property).1).1
  have hh := residual_profile_at_support S hp F R B.val hb (Finset.mem_filter.mp B.property).1
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (fun v=>tupleWeight H v*ψ (finiteTupleProduct v))
  calc
    _ = (frozenWeight H B.val*allocationTerm D Finset.univ B.val a*ψ (finiteTupleProduct B.val))*
        ∑u∈residualBoxes S F B.val hb,
          profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1 (fun j=>B.val j*u j)*
            (tupleWeight H (remainingTuple B.val u)*ψ (finiteTupleProduct (remainingTuple B.val u))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      dsimp only [c]
      rw [fixed_weight_split H S hS hp F hF B u hu,
        artificial_projector_frozen D F hDF Finset.univ a B.val u
          (fun j=>(Finset.mem_filter.mp (Fintype.mem_piFinset.mp hu j)).2)]
      have hf := actual_frozen_slots S hS F hF B.val hb
        (allocation_data S F B.val (Finset.mem_filter.mp B.property).1).2 u hu hp
      have he : finiteTupleProduct (fun j=>B.val j*u j)=
          finiteTupleProduct B.val*finiteTupleProduct (remainingTuple B.val u) := by
        rw [finiteTupleProduct,Finset.prod_mul_distrib]
        exact congrArg (fun x=>finiteTupleProduct B.val*x) (remaining_product B.val u hf)
      rw [he,map_mul]
      ring
    _ = _ := by
      rw [hh]
      have he : (∑v∈liveBox S B.val hb,
          liveProfile B.val F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v*
            (tupleWeight H v*ψ (finiteTupleProduct v)))=
          ∑v∈liveBox S B.val hb,
            tupleWeight H v*liveProfile B.val F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v*
              ψ (finiteTupleProduct v) := by
        apply Finset.sum_congr rfl
        intro v hv
        ring
      rw [he]
      ring

/-- Positive-energy transfer preserving the squared frozen coefficients.
The extracted character phase costs at most one, independently of the row.
The factor counting fixed-support labels has the proved subpower bound. -/
theorem allocated_restricted_energy (H : Id) (S : (ι⊕Fin 2)→Finset Id)
    (hS : ∀j,∀I∈S j,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (D F R : Id) (hF : F≠0) (hDF : D∣F)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (ψ : Id→*ℂ) (hψ : ∀I,‖ψ I‖≤1)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id) :
    ‖∑v∈Fintype.piFinset S,tupleWeight H v*allocationTerm D Finset.univ v a*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1 v*ψ (finiteTupleProduct v)‖^2≤
      ((boundedLabels S F).card:ℝ)*∑B : boundedLabels S F,
        ‖frozenWeight H B.val*allocationTerm D Finset.univ B.val a*
          frozenCoefficient B.val (finiteTupleProduct B.val) R ν Wslot P‖^2*
        ‖∑v∈liveBox S B.val (allocation_data S F B.val (Finset.mem_filter.mp B.property).1).1,
          tupleWeight H v*liveProfile B.val F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v*
            ψ (finiteTupleProduct v)‖^2 := by
  rw [allocated_restricted_character_sum H S hS hp D F R hF hDF a ψ
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂]
  let A := fun B : boundedLabels S F=>frozenWeight H B.val*allocationTerm D Finset.univ B.val a*
    frozenCoefficient B.val (finiteTupleProduct B.val) R ν Wslot P
  let G := fun B : boundedLabels S F=>
    ∑v∈liveBox S B.val (allocation_data S F B.val (Finset.mem_filter.mp B.property).1).1,
      tupleWeight H v*liveProfile B.val F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v*
        ψ (finiteTupleProduct v)
  have hh := CubicEisenstein.norm_sum_sq_le_card Finset.univ
    (fun B : boundedLabels S F=>A B*ψ (finiteTupleProduct B.val)*G B)
  apply hh.trans
  simp only [Finset.card_univ,Fintype.card_coe]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro B hB
  change ‖A B*ψ (finiteTupleProduct B.val)*G B‖^2≤‖A B‖^2*‖G B‖^2
  rw [norm_mul,norm_mul,mul_pow,mul_pow]
  have hc : ‖ψ (finiteTupleProduct B.val)‖^2≤1 := by
    nlinarith [hψ (finiteTupleProduct B.val),norm_nonneg (ψ (finiteTupleProduct B.val))]
  calc
    _ ≤ (‖A B‖^2*1)*‖G B‖^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by ring

end
end Candidate.SilPrior.FourthPower.MixedArtificialRestriction
