/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussPayments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedCubeGaussPaymentLift_f0d3a654bc986937_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

/-- Restore the frozen marked coordinates as units, so the native primary
allocation has the same literal index domain as the common allocation. -/
def liftPrimaryTuple (B : Tuple ι) (E : Tuple (liveIndices B)) : Tuple ι :=
  Sum.elim (fun i=>if hi:i∈liveIndices B then E (Sum.inl ⟨i,hi⟩) else 1)
    (fun j=>E (Sum.inr j))

@[simp] lemma liftPrimaryTuple_ordinary (B : Tuple ι) (E : Tuple (liveIndices B)) (j : Fin 2) :
    liftPrimaryTuple B E (Sum.inr j)=E (Sum.inr j) := rfl

lemma liftPrimaryTuple_nonzero (B : Tuple ι) (E : Tuple (liveIndices B))
    (hE : ∀j,E j≠0) : ∀j,liftPrimaryTuple B E j≠0 := by
  intro j
  cases j with
  | inl i=>
    unfold liftPrimaryTuple
    simp only [Sum.elim_inl]
    split_ifs
    · exact hE _
    · exact one_ne_zero
  | inr j=>exact hE _

lemma liftPrimaryTuple_product (B : Tuple ι) (E : Tuple (liveIndices B)) :
    finiteTupleProduct (liftPrimaryTuple B E)=finiteTupleProduct E := by
  unfold finiteTupleProduct
  rw [Fintype.prod_sum_type,Fintype.prod_sum_type]
  apply congrArg (fun z:Id=>z*(∏j:Fin 2,E (Sum.inr j)))
  let f : ι→Id:=fun i=>if hi:i∈liveIndices B then E (Sum.inl ⟨i,hi⟩) else 1
  change (∏i,f i)=∏i:liveIndices B,E (Sum.inl i)
  calc
    _ = ∏i∈liveIndices B,f i :=
      (Finset.prod_subset (Finset.subset_univ _) (fun i _ hn=>by simp [f,hn])).symm
    _ = ∏i:liveIndices B,f i := (Finset.prod_coe_sort (liveIndices B) f).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      simp [f,i.property]

lemma primary_common_product (r : Source ι a b) (G L : Id)
    (B : commonAlloc r G) (E : fullPrimaryAlloc r G B L) :
    (∏j,B.val j*liftPrimaryTuple B.val E.val j)=G*finiteTupleProduct E.val := by
  rw [Finset.prod_mul_distrib]
  change finiteTupleProduct B.val*finiteTupleProduct (liftPrimaryTuple B.val E.val)=_
  rw [commonAlloc_product,liftPrimaryTuple_product]

lemma primary_prefix_left (r : Source ι a b) (G L : Id)
    (B : commonAlloc r G) (E : fullPrimaryAlloc r G B L) :
    r.d.1*(B.val (Sum.inr 0)*liftPrimaryTuple B.val E.val (Sum.inr 0))=
      (primaryOrdinaryPrefix r G L B E).1 := by
  unfold primaryOrdinaryPrefix commonLiveD
  simp only [Prod.fst,Prod.snd,liftPrimaryTuple_ordinary]
  exact (mul_assoc r.d.1 (B.val (Sum.inr 0)) (E.val (Sum.inr 0))).symm

lemma primary_prefix_right (r : Source ι a b) (G L : Id)
    (B : commonAlloc r G) (E : fullPrimaryAlloc r G B L) :
    r.d.2*(B.val (Sum.inr 1)*liftPrimaryTuple B.val E.val (Sum.inr 1))=
      (primaryOrdinaryPrefix r G L B E).2 := by
  unfold primaryOrdinaryPrefix commonLiveD
  simp only [Prod.fst,Prod.snd,liftPrimaryTuple_ordinary]
  exact (mul_assoc r.d.2 (B.val (Sum.inr 1)) (E.val (Sum.inr 1))).symm

#print axioms liftPrimaryTuple_nonzero
#print axioms liftPrimaryTuple_product
#print axioms primary_common_product
#print axioms primary_prefix_left
#print axioms primary_prefix_right
end
end QRH.Cycle092.FixedCubeGauss
