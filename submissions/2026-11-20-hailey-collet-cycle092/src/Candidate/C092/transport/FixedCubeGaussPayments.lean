/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Exact finite indices and multiplicities for the native fixed allocation. -/
import Candidate.C092.transport.FixedCubeGaussH8Projection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedCubeGaussPayments_2ba5d6d7c1ffaeed_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

lemma commonAlloc_product (r : Source ι a b) (G : Id) (B : commonAlloc r G) :
    finiteTupleProduct B.val=G := (Finset.mem_filter.mp B.property).2

lemma commonAlloc_card (r : Source ι a b) (G : Id) (hG : G≠0) :
    (commonAlloc r G).card≤(idealDivisors G).card^Fintype.card (ι⊕Fin 2) :=
  actualAllocations_card (sourcePools r) G hG

lemma fullPrimaryAlloc_card (r : Source ι a b) (G L : Id) (hL : L≠0) (B : commonAlloc r G) :
    (fullPrimaryAlloc r G B L).card≤
      (idealDivisors (L^4)).card^Fintype.card (liveIndices B.val⊕Fin 2) :=
  MixedFixedSupport.bounded_labels_card (primaryPools r G B) L hL

lemma fullPrimaryAlloc_coordinate_divides (r : Source ι a b) (G L : Id)
    (B : commonAlloc r G) (E : fullPrimaryAlloc r G B L) (j : liveIndices B.val⊕Fin 2) :
    E.val j∣L^4 := (Finset.mem_filter.mp E.property).2 j

lemma signedPrimaryAlloc_card (r : Source ι a b) (G L : Id) (B : commonAlloc r G) :
    Fintype.card (Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)))≤
      (2^(primeSupport L).card)^Fintype.card (liveIndices B.val⊕Fin 2) := by
  simpa only [Finset.card_univ] using allocation_card_bound L (Finset.univ : Finset (liveIndices B.val⊕Fin 2))

lemma live_slots_card_le (r : Source ι a b) (G : Id) (B : commonAlloc r G) :
    Fintype.card (liveIndices B.val⊕Fin 2)≤Fintype.card (ι⊕Fin 2) := by
  simp only [Fintype.card_sum]
  exact Nat.add_le_add_right (Fintype.card_subtype_le (fun i:ι=>i∈liveIndices B.val)) _

/-- An active signed allocation pays the entire squarefree second divisor.
Zero allocation terms remain in the original sum and require no restriction. -/
lemma allocationTerm_ne_zero_divides {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : Id) (hL : Squarefree L) (v : κ→Id)
    (aL : Allocation L (Finset.univ : Finset κ))
    (haL : allocationTerm L Finset.univ v aL≠0) : L∣∏j,v j := by
  apply (squarefree_dvd_iff L _ hL).mpr
  intro P hP
  let p : primeSupport L := ⟨P,hP⟩
  have hp : (-1:ℂ)^((aL p).val.card+1)*
      (∏i∈(aL p).val,if P∣v i then (1:ℂ) else 0)≠0 :=
    Finset.prod_ne_zero_iff.mp haL p (Finset.mem_univ _)
  have hne : (aL p).val.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (Finset.mem_erase.mp (aL p).property).1
  obtain ⟨i,hi⟩ := hne
  have hit : (if P∣v i then (1:ℂ) else 0)≠0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hp) i hi
  have hd : P∣v i := by
    by_contra hh
    exact hit (ite_eq_right hh)
  exact hd.trans (Finset.dvd_prod_of_mem v (Finset.mem_univ i))

#print axioms allocationTerm_ne_zero_divides
#print axioms live_slots_card_le
#print axioms commonAlloc_product
#print axioms commonAlloc_card
#print axioms fullPrimaryAlloc_card
#print axioms fullPrimaryAlloc_coordinate_divides
#print axioms signedPrimaryAlloc_card
end
end QRH.Cycle092.FixedCubeGauss
