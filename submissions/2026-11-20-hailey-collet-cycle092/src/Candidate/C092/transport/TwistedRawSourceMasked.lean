/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Exact signed divisor mask after common extraction, with both live colors. -/
import Candidate.C092.transport.TwistedRawSourcePrimary
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawSource
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceRectangle
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentFirstSectors
open CenteredMomentCommonAllocationBox CenteredMomentDivisorAllocation
open QRH.SilDensitySplit.CubeFree.FP
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance (priority := 2000) sumMaskedDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _

private theorem weighted_mask_allocation {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : Id) (hL : Squarefree L) (v : κ → Id) (c : ℂ) :
    (if L ∣ ∏ j, v j then c else 0) =
      ∑ a : Allocation L (Finset.univ : Finset κ), c * allocationTerm L Finset.univ v a := by
  have h := congrArg (fun z : ℂ => c*z) (squarefree_mask_allocation L hL Finset.univ v)
  simpa only [Finset.mul_sum, mul_ite, mul_one, mul_zero] using h

def maskedLiveSum (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (S H : Finset QRH.Record1252270103KernelMass.PrimeIdeal)
    (pool : ι → Finset Id) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (B : Tuple ι) (hB : ∀ j, B j ≠ 0) (G R L : Id)
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑ v ∈ liveBox (MixedLiteralAllocation.sourcePools pool d hd b X₁ X₂ Y₁ Y₂) B hB,
    (if L ∣ finiteTupleProduct v then
      MixedCommonCoefficient.tupleWeight (MixedCommonRestriction.punctureProduct S H) v *
        ordinaryColor ω₁ ω₂ v * liveProfile B G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 v
      else 0) * idealCoeff χ (finiteTupleProduct v)

/-- The signed nonempty-subset allocations expand the genuine full divisor
    mask. The following allocatedRow performs the full L-primary extraction. -/
theorem masked_live_sum (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (S H : Finset QRH.Record1252270103KernelMass.PrimeIdeal)
    (pool : ι → Finset Id) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (B : Tuple ι) (hB : ∀ j, B j ≠ 0) (G R L : Id) (hL : Squarefree L)
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    MixedLiveNormalization.normalization (X₁*X₂) (fun i : liveIndices B => P i.val) *
      maskedLiveSum ω₁ ω₂ χ S H pool d hd B hB G R L ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ =
      ∑ a : Allocation L (Finset.univ : Finset (liveIndices B ⊕ Fin 2)),
        allocatedRow ω₁ ω₂ χ S H (fun i : liveIndices B => pool i.val)
          (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))
          ⟨mul_ne_zero hd.1 (hB _),mul_ne_zero hd.2 (hB _)⟩ L (R*G) a
          (fun i => ν i.val) (fun i => Wslot i.val) (fun i => P i.val)
          W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  unfold maskedLiveSum allocatedRow MixedLiteralAllocation.sourcePools
  rw [MixedLiveRows.source_live_box pool d hd _ _ B hB]
  unfold liveProfile
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  let c : ℂ := MixedLiveNormalization.normalization (X₁*X₂) (fun i : liveIndices B => P i.val) *
    (MixedCommonCoefficient.tupleWeight (MixedCommonRestriction.punctureProduct S H) v *
      ordinaryColor ω₁ ω₂ v *
      profileCoefficient (R*G) (fun i : liveIndices B => ν i.val) (fun i => Wslot i.val)
        (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂ (d.1*B (Sum.inr 0)) (d.2*B (Sum.inr 1)) 1 v *
      idealCoeff χ (finiteTupleProduct v))
  calc
    _ = if L ∣ finiteTupleProduct v then c else 0 := by dsimp only [c]; split_ifs <;> ring
    _ = ∑ a : Allocation L (Finset.univ : Finset (liveIndices B ⊕ Fin 2)),
        c * allocationTerm L Finset.univ v a := weighted_mask_allocation L hL v c
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      dsimp only [c]
      ring

#print axioms masked_live_sum
end
end QRH.Cycle092.TwistedRawSource
