/- Copyright (c) 2026 Sil. Apache-2.0.
Complete common extraction of the actual restricted ordinary/marked tuple.
Use baseline's genuine allocation boxes and remainingTuple. Both marked
injectivity and ordinary fifth-freeness are split exactly, not majorized.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedCommonRestriction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonProfile

set_option autoImplicit false
namespace Candidate.FourthPower.MixedCommonAllocation
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox CenteredMomentCommonPrimeSlots
open MixedCommonRestriction
local notation "Id" => Ideal ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def slotProduct (v : Tuple ι) : Id := ∏i,v (Sum.inl i)
def frozenIndices (B : Tuple ι) : Finset ι := Finset.univ.filter (fun i=>B (Sum.inl i)≠1)

def tupleRestriction (H : Id) (v : Tuple ι) : Prop :=
  restriction H (slotProduct v) (v (Sum.inr 0)) (v (Sum.inr 1)) ∧
    Function.Injective (fun i=>v (Sum.inl i))

def frozenRestriction (H : Id) (B : Tuple ι) : Prop :=
  restriction H (slotProduct B) (B (Sum.inr 0)) (B (Sum.inr 1)) ∧
    Set.InjOn (fun i=>B (Sum.inl i)) (frozenIndices B)

theorem slot_product_remaining (B u : Tuple ι)
    (hf : ∀i,B (Sum.inl i)≠1→u (Sum.inl i)=1) :
    slotProduct u=slotProduct (remainingTuple B u) := by
  unfold slotProduct
  simp only [remainingTuple_slot]
  rw [Finset.prod_coe_sort (liveIndices B) (fun i=>u (Sum.inl i))]
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro i hi hn
  exact hf i (fun hh=>hn (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hh⟩))

theorem slot_product_reconstruct (B u : Tuple ι)
    (hf : ∀i,B (Sum.inl i)≠1→u (Sum.inl i)=1) :
    slotProduct (fun j=>B j*u j)=slotProduct B*slotProduct (remainingTuple B u) := by
  rw [slotProduct,Finset.prod_mul_distrib]
  exact congrArg (fun x=>slotProduct B*x) (slot_product_remaining B u hf)

theorem injective_split (B u : Tuple ι) (C : Id)
    (hprod : finiteTupleProduct B=C)
    (hf : ∀i,B (Sum.inl i)≠1→u (Sum.inl i)=1)
    (hp : ∀i,Prime (B (Sum.inl i)*u (Sum.inl i)))
    (hc : ∀j,IsCoprime C (u j)) :
    Function.Injective (fun i=>B (Sum.inl i)*u (Sum.inl i)) ↔
      Set.InjOn (fun i=>B (Sum.inl i)) (frozenIndices B) ∧
      Function.Injective (fun i : liveIndices B=>u (Sum.inl i.val)) := by
  have hcross (i j : ι) (hi : B (Sum.inl i)≠1) (hj : B (Sum.inl j)=1) :
      B (Sum.inl i)*u (Sum.inl i)≠B (Sum.inl j)*u (Sum.inl j) := by
    rw [hf i hi,mul_one,hj,one_mul]
    intro he
    have hpi : Prime (B (Sum.inl i)) := by simpa only [hf i hi,mul_one] using hp i
    have hd : B (Sum.inl i)∣C := by
      rw [←hprod]
      exact Finset.dvd_prod_of_mem B (Finset.mem_univ _)
    exact hpi.not_isUnit ((hc (Sum.inl j)).isUnit_of_dvd' hd (he ▸ dvd_rfl))
  constructor
  · intro h
    constructor
    · intro i hi j hj he
      apply h
      dsimp only at he ⊢
      rw [hf i (Finset.mem_filter.mp hi).2,hf j (Finset.mem_filter.mp hj).2,mul_one,mul_one,he]
    · intro i j he
      apply Subtype.ext
      apply h
      dsimp only at he ⊢
      rw [(Finset.mem_filter.mp i.property).2,(Finset.mem_filter.mp j.property).2,one_mul,one_mul]
      exact he
  · rintro ⟨hF,hL⟩ i j he
    by_cases hi : B (Sum.inl i)=1
    · by_cases hj : B (Sum.inl j)=1
      · have hh := hL (a₁:=⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩)
          (a₂:=⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩) (by simpa only [hi,hj,one_mul] using he)
        exact congrArg Subtype.val hh
      · exact False.elim (hcross j i hj hi he.symm)
    · by_cases hj : B (Sum.inl j)=1
      · exact False.elim (hcross i j hi hj he)
      · apply hF (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
        simpa only [hf i hi,hf j hj,mul_one] using he

theorem tuple_restriction_split (H C : Id) (B u : Tuple ι)
    (hB : ∀j,B j≠0) (hu : ∀j,u j≠0) (hprod : finiteTupleProduct B=C)
    (hf : ∀i,B (Sum.inl i)≠1→u (Sum.inl i)=1)
    (hp : ∀i,Prime (B (Sum.inl i)*u (Sum.inl i)))
    (hc : ∀j,IsCoprime C (u j)) :
    tupleRestriction H (fun j=>B j*u j) ↔
      frozenRestriction H B ∧ tupleRestriction H (remainingTuple B u) := by
  have he : slotProduct B*(B (Sum.inr 0)*B (Sum.inr 1))=C := by
    simpa only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,slotProduct] using hprod
  have hBC : B (Sum.inr 0)*B (Sum.inr 1)∣C := by
    rw [←he]
    exact dvd_mul_left _ _
  have hFC : slotProduct B∣C := by rw [←he];exact dvd_mul_right _ _
  have hCI := (hc (Sum.inr 0)).mul_right (hc (Sum.inr 1))
  have hCL : IsCoprime C (slotProduct (remainingTuple B u)) :=
    IsCoprime.prod_right (fun i _=>hc (Sum.inl i.val))
  unfold tupleRestriction frozenRestriction
  rw [slot_product_reconstruct B u hf,restriction_split_common H C _ _ _ _ _ _
    (mul_ne_zero (hB _) (hB _)) (mul_ne_zero (hu _) (hu _)) hBC hFC hCI hCL,
    injective_split B u C hprod hf hp hc]
  simp only [remainingTuple_plain,remainingTuple_slot]
  tauto

/-- Every structural premise above is supplied by the actual common
allocation and residual box. No hypothesis on a replacement vector. -/
theorem actual_restriction_split (H : Id) (S : (ι⊕Fin 2)→Finset Id)
    (hS : ∀j,∀I∈S j,I≠0) (C : Id) (hC : C≠0)
    (B : actualAllocations S C) (u : Tuple ι)
    (hu : u∈residualBoxes S C B.val
      (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).1)
    (hp : ∀i,∀I∈S (Sum.inl i),Prime I) :
    tupleRestriction H (fun j=>B.val j*u j) ↔
      frozenRestriction H B.val ∧ tupleRestriction H (remainingTuple B.val u) := by
  have hB := allocation_data S C B.val (Finset.mem_filter.mp B.property).1
  apply tuple_restriction_split H C B.val u hB.1
    (fun j=>right_ne_zero_of_mul (hS j _ (residual_original_mem S C B.val hB.1 u hu j)))
    (Finset.mem_filter.mp B.property).2
    (actual_frozen_slots S hS C hC B.val hB.1 hB.2 u hu hp)
    (fun i=>hp i _ (residual_original_mem S C B.val hB.1 u hu (Sum.inl i)))
    (fun j=>(Finset.mem_filter.mp (Fintype.mem_piFinset.mp hu j)).2)

end
end Candidate.FourthPower.MixedCommonAllocation
