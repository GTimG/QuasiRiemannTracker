/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Full primary allocations retain the independent ordinary colors. -/
import Candidate.C092.transport.TwistedRawSourceFrozen
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawSource
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentFirstSectors
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox CenteredMomentDivisorAllocation
open QRH.SilDensitySplit.CubeFree.FP
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance (priority := 2000) sumAllocatedDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _
local instance (priority := 2000) subtypeAllocatedDecEq {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

theorem colored_allocated_restricted_sum
    (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character) (H : Id)
    (S : (ι ⊕ Fin 2) → Finset Id) (hS : ∀ j, ∀ I ∈ S j, I ≠ 0)
    (hp : ∀ i, ∀ I ∈ S (Sum.inl i), Prime I)
    (D F R : Id) (hF : F ≠ 0) (hDF : D ∣ F)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id) :
    (∑ v ∈ Fintype.piFinset S,
      MixedCommonCoefficient.tupleWeight H v * ordinaryColor ω₁ ω₂ v *
        allocationTerm D Finset.univ v a *
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1 v *
        idealCoeff χ (finiteTupleProduct v)) =
      ∑ B : MixedFixedSupport.boundedLabels S F,
        MixedCommonCoefficient.frozenWeight H B.val * ordinaryColor ω₁ ω₂ B.val *
          allocationTerm D Finset.univ B.val a *
          frozenCoefficient B.val (finiteTupleProduct B.val) R ν Wslot P *
          idealCoeff χ (finiteTupleProduct B.val) *
        ∑ v ∈ liveBox S B.val (allocation_data S F B.val (Finset.mem_filter.mp B.property).1).1,
          MixedCommonCoefficient.tupleWeight H v * ordinaryColor ω₁ ω₂ v *
            liveProfile B.val F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v *
            idealCoeff χ (finiteTupleProduct v) := by
  let c : Tuple ι → ℂ := fun v => MixedCommonCoefficient.tupleWeight H v *
    ordinaryColor ω₁ ω₂ v * allocationTerm D Finset.univ v a *
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1 v *
    idealCoeff χ (finiteTupleProduct v)
  have hc : ∀ v ∈ Fintype.piFinset S, c v ≠ 0 →
      Candidate.FourthPower.SexticSieve.PowerFree 3 (∏ j, v j) := by
    intro v hv hn
    have htw : MixedCommonCoefficient.tupleWeight H v ≠ 0 := by
      intro hz
      exact hn (by simp only [c, hz, zero_mul])
    have hr : MixedCommonAllocation.tupleRestriction H v := by
      by_contra hh
      exact htw (by simp only [MixedCommonCoefficient.tupleWeight, hh, ite_false])
    exact MixedArtificialRestriction.restricted_tuple_fifth_free H v
      (fun j => hS j _ (Fintype.mem_piFinset.mp hv j))
      (fun i => hp i _ (Fintype.mem_piFinset.mp hv (Sum.inl i))) hr
  have hs := MixedFixedSupport.bounded_residual_sum S hS F hF c hc
  change (∑ v ∈ Fintype.piFinset S, c v) = _
  rw [hs]
  apply Finset.sum_congr rfl
  intro B hmem
  let hB := (allocation_data S F B.val (Finset.mem_filter.mp B.property).1).1
  let f := fun v : Tuple (liveIndices B.val) =>
    MixedCommonCoefficient.tupleWeight H v * ordinaryColor ω₁ ω₂ v * idealCoeff χ (finiteTupleProduct v)
  have hprof := MixedArtificialRestriction.residual_profile_at_support S hp F R B.val hB
    (Finset.mem_filter.mp B.property).1 ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f
  calc
    _ = (MixedCommonCoefficient.frozenWeight H B.val * ordinaryColor ω₁ ω₂ B.val *
        allocationTerm D Finset.univ B.val a * idealCoeff χ (finiteTupleProduct B.val)) *
      ∑ u ∈ residualBoxes S F B.val hB,
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1 (fun j => B.val j*u j) *
          f (remainingTuple B.val u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      have hcop : ∀ j, IsCoprime F (u j) :=
        fun j => (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hu j)).2
      have hf := actual_frozen_slots S hS F hF B.val hB
        (allocation_data S F B.val (Finset.mem_filter.mp B.property).1).2 u hu hp
      have hprod : finiteTupleProduct (fun j => B.val j*u j) =
          finiteTupleProduct B.val * finiteTupleProduct (remainingTuple B.val u) := by
        unfold finiteTupleProduct
        rw [Finset.prod_mul_distrib]
        change finiteTupleProduct B.val * finiteTupleProduct u = _
        rw [remaining_product B.val u hf]
        rfl
      dsimp only [c, f]
      rw [MixedArtificialRestriction.fixed_weight_split H S hS hp F hF B u hu,
        ordinaryColor_allocation, MixedFixedSupport.artificial_projector_frozen D F hDF
          Finset.univ a B.val u hcop, hprod, map_mul]
      ring
    _ = _ := by
      rw [hprof]
      have he : (∑ v ∈ liveBox S B.val hB,
          liveProfile B.val F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v * f v) =
          ∑ v ∈ liveBox S B.val hB,
            MixedCommonCoefficient.tupleWeight H v * ordinaryColor ω₁ ω₂ v *
              liveProfile B.val F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v *
              idealCoeff χ (finiteTupleProduct v) := by
        apply Finset.sum_congr rfl
        intro v hv
        dsimp only [f]
        ring
      rw [he]
      ring

#print axioms colored_allocated_restricted_sum
end
end QRH.Cycle092.TwistedRawSource
