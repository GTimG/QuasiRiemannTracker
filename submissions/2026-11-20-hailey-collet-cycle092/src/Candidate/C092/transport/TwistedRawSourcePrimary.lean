/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The literal independently colored primary row and canonical endpoint. -/
import Candidate.C092.transport.TwistedRawSourceAllocated
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
local instance (priority := 2000) sumPrimaryDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _
local instance (priority := 2000) subtypePrimaryDecEq {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

def allocatedRow (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (S H : Finset QRH.Record1252270103KernelMass.PrimeIdeal)
    (pool : ι → Finset Id) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) (D R : Id)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  MixedLiveNormalization.normalization (X₁*X₂) P *
    ∑ v ∈ Fintype.piFinset (MixedLiteralAllocation.sourcePools pool d hd b X₁ X₂ Y₁ Y₂),
      MixedCommonCoefficient.tupleWeight (MixedCommonRestriction.punctureProduct S H) v *
        ordinaryColor ω₁ ω₂ v * allocationTerm D Finset.univ v a *
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v *
        idealCoeff χ (finiteTupleProduct v)

theorem allocated_row_identity (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (S H : Finset QRH.Record1252270103KernelMass.PrimeIdeal)
    (pool : ι → Finset Id) (hp : ∀ i, ∀ I ∈ pool i, Prime I)
    (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) (D F R : Id) (hF : F ≠ 0) (hDF : D ∣ F)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    allocatedRow ω₁ ω₂ χ S H pool d hd D R a ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ =
      ∑ B : MixedFixedSupport.boundedLabels
          (MixedLiteralAllocation.sourcePools pool d hd b X₁ X₂ Y₁ Y₂) F,
        MixedCommonCoefficient.frozenWeight (MixedCommonRestriction.punctureProduct S H) B.val *
          ordinaryColor ω₁ ω₂ B.val * allocationTerm D Finset.univ B.val a *
          idealCoeff χ (finiteTupleProduct B.val) *
          frozenRow ω₁ ω₂ χ S H pool d hd B.val
            (allocation_data _ F B.val (Finset.mem_filter.mp B.property).1).1
            F R ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  unfold allocatedRow
  rw [colored_allocated_restricted_sum ω₁ ω₂ χ _ _
    (MixedLiteralAllocation.source_pools_nonzero pool hp d hd b X₁ X₂ Y₁ Y₂)
    (by intro i I hI; exact hp i I hI) D F R hF hDF a ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  unfold frozenRow frozenLiveSum
  ring

/-- The full primary endpoint retains the entire F puncture and both colors
    on the residual ordinary ideals. No conductor-divisibility gate is added. -/
theorem allocated_row_canonical (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (S H : Finset QRH.Record1252270103KernelMass.PrimeIdeal)
    (pool : ι → Finset Id) (hp : ∀ i, ∀ I ∈ pool i, Prime I)
    (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) (D F R : Id) (hF : F ≠ 0) (hDF : D ∣ F)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    allocatedRow ω₁ ω₂ χ S H pool d hd D R a ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ =
      ∑ B : MixedFixedSupport.boundedLabels
          (MixedLiteralAllocation.sourcePools pool d hd b X₁ X₂ Y₁ Y₂) F,
        (MixedCommonCoefficient.frozenWeight (MixedCommonRestriction.punctureProduct S H) B.val *
          ordinaryColor ω₁ ω₂ B.val * allocationTerm D Finset.univ B.val a *
          idealCoeff χ (finiteTupleProduct B.val) *
          MixedLiveNormalization.normalization (X₁*X₂) P *
          frozenCoefficient B.val (finiteTupleProduct B.val) R ν Wslot P) *
        canonicalSource ω₁ ω₂ χ S H (R*F) (fun i : liveIndices B.val => pool i.val)
          (fun i => ν i.val) (fun i => Wslot i.val) (fun i => P i.val)
          W₁ W₂ b X₁ X₂ Y₁ Y₂ (d.1*B.val (Sum.inr 0), d.2*B.val (Sum.inr 1)) := by
  rw [allocated_row_identity ω₁ ω₂ χ S H pool hp d hd D F R hF hDF a ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂]
  apply Finset.sum_congr rfl
  intro B hB
  unfold frozenRow
  rw [frozen_live_eq_canonical]
  ring

#print axioms allocated_row_identity
#print axioms allocated_row_canonical
end
end QRH.Cycle092.TwistedRawSource
