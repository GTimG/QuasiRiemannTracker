/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Literal independently colored allocated live rows, signed divisor masks,
genuine common allocations and original residual-column row dictionary.
Adapted from Sil mixed-source identities and the shared TwistedRawBall
arbitrary-kernel common allocation identity.
-/
import Candidate.C092.transport.RegularColoredFrameAllocated
import Candidate.C092.transport.TwistedRawSourceMasked
import Candidate.C092.transport.TwistedRawBallDictionary
import Candidate.C092.transport.TwistedRawSourcePrimary
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedCommonSource
import Submissions.sil_density_split_20261026.CubeFree.Packet.Reduce.MixedOriginalSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace QRH.Cycle092.RegularColoredForward
open Candidate.FourthPower.KernelAssignmentReindex Candidate.FourthPower.NativeFiniteHoles Candidate.FourthPower.KernelNaturalSlots
open QRH.SilDensitySplit.CubeFree.FP
open QRH.SilDensitySplit.CubeFree.Packet.Reduce

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferencePrimeEnclosure MixedCompletedRows
open NativeInjectiveEnergy
open MixedCenteredEnergy MixedLiveRows MixedLiveNormalization MixedCanonicalSource
open MixedUniformSource MixedFrozenSource MixedSourceAssembly MixedAllocationCost
open MixedAllocationSource MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open MixedAllocatedEnergy MixedUniformAllocated MixedCommonAllocated MixedDivisorMask
open MixedCommonMasked MixedCommonSource MixedOriginalSource MixedRestrictedDictionary
open MixedFixedSupport
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor HeckeDyadic CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentSourceRectangle CenteredMomentSourceMass
open CenteredMomentCommonAllocationBox CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorEnergy
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance c092LocalInst_Candidate_C092_transport_RegularColoredFrameDictionary_2f34933381e3b62a_001 {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable {α : Type*} [Fintype α]
def frameAllocatedLiveSum (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (B : Tuple α) (hB : ∀j,B j≠0) (G R D : Id)
    (allocation : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2)))
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑v∈liveBox (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) B hB,
    tupleWeight (punctureProduct S H) v*TwistedRawSource.ordinaryColor ω₁ ω₂ v*allocationTerm D Finset.univ v allocation*
      liveProfile B G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 v*
      idealCoeff χ (finiteTupleProduct v)

theorem frame_allocated_live_row (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (B : Tuple α) (hB : ∀j,B j≠0) (G R D : Id)
    (allocation : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2)))
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    normalization (X₁*X₂) (fun i : liveIndices B=>P i.val)*
      frameAllocatedLiveSum ω₁ ω₂ χ S H pool d hd B hB G R D allocation ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂=
    TwistedRawSource.allocatedRow ω₁ ω₂ χ S H (fun i : liveIndices B=>pool i.val)
      (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))
      ⟨mul_ne_zero hd.1 (hB _),mul_ne_zero hd.2 (hB _)⟩ D (R*G) allocation
      (fun i=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val) W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  unfold frameAllocatedLiveSum sourcePools
  rw [source_live_box pool d hd (plainSupportPool b X₁ Y₁) (plainSupportPool b X₂ Y₂) B hB]
  unfold TwistedRawSource.allocatedRow sourcePools liveProfile
  apply congrArg (fun x : ℂ=>normalization (X₁*X₂) (fun i : liveIndices B=>P i.val)*x)
  apply Finset.sum_congr
  · ext v;simp only [Fintype.mem_piFinset]
  · intro v hv;rfl


theorem frame_masked_live_sum (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (B : Tuple α) (hB : ∀j,B j≠0) (G R D : Id)
    (hD : Squarefree D) (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    TwistedRawSource.maskedLiveSum ω₁ ω₂ χ S H pool d hd B hB G R D ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂=
      ∑a : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2)),
        frameAllocatedLiveSum ω₁ ω₂ χ S H pool d hd B hB G R D a ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  have he := finite_mask_regroup D hD (Finset.univ : Finset (liveIndices B⊕Fin 2))
    (liveBox (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) B hB) id
    (fun (_ : Unit) v=>tupleWeight (punctureProduct S H) v*TwistedRawSource.ordinaryColor ω₁ ω₂ v*
      liveProfile B G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 v*
      idealCoeff χ (finiteTupleProduct v)) ()
  refine (Eq.trans ?_ he).trans ?_
  · unfold TwistedRawSource.maskedLiveSum
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [finiteTupleProduct,id_eq]
    split_ifs <;> ring
  · apply Finset.sum_congr rfl
    intro a ha
    unfold allocatedPolynomial frameAllocatedLiveSum
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [id_eq]
    ring

def frameCommonMaskedRow (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (G R D : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑B : actualAllocations (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) G,
    frozenWeight (punctureProduct S H) B.val*TwistedRawSource.ordinaryColor ω₁ ω₂ B.val*
      (normalization (X₁*X₂) P*(frozenCoefficient B.val G R ν Wslot P*
        TwistedRawSource.maskedLiveSum ω₁ ω₂ χ S H pool d hd B.val
          (allocation_data _ G B.val (Finset.mem_filter.mp B.property).1).1 G R D
          ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂))

def frameOriginalMaskedRow (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (G R seed D : Id) (hG : G≠0)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  normalization (X₁*X₂) P*
    ∑I∈residualPool G hG (finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))),
      (if IsCoprime G I ∧ D∣I then finiteColumnCoefficient
        (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
        (fun v=>tupleWeight (punctureProduct S H) v*TwistedRawSource.ordinaryColor ω₁ ω₂ v*profileCoefficient R ν Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ d.1 d.2 seed v) (G*I) else 0)*idealCoeff χ I

theorem frame_original_masked_row_eq {α : Type*} [Fintype α]
    (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character) (S H : Finset PrimeIdeal)
    (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (G R seed D : Id) (hG : G≠0) (hseed : seed∣G)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    frameOriginalMaskedRow ω₁ ω₂ χ S H pool d hd G R seed D hG ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ =
      frameCommonMaskedRow ω₁ ω₂ χ S H pool d hd G R D ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  have he := TwistedRawBall.common_masked_column_sum ω₁ ω₂ (punctureProduct S H)
    (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) (source_pools_nonzero pool hp d hd b X₁ X₂ Y₁ Y₂)
    (fun i I hI=>hp i I hI) G R seed D hG hseed ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 (idealCoeff χ)
  unfold frameOriginalMaskedRow frameCommonMaskedRow
  change normalization (X₁*X₂) P * _ = _
  unfold TwistedRawSource.coloredColumn TwistedRawSource.coloredTuple at he
  rw [he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hh : (∑ v ∈ liveBox (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) B.val
      (allocation_data _ G B.val (Finset.mem_filter.mp B.property).1).1,
      if D ∣ finiteTupleProduct v then TwistedRawSource.coloredTuple (punctureProduct S H) ω₁ ω₂
        (liveProfile B.val G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2) v * idealCoeff χ (finiteTupleProduct v)
        else 0) = TwistedRawSource.maskedLiveSum ω₁ ω₂ χ S H pool d hd B.val
          (allocation_data _ G B.val (Finset.mem_filter.mp B.property).1).1 G R D
          ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
    unfold TwistedRawSource.maskedLiveSum
    apply Finset.sum_congr rfl
    intro v hv
    unfold TwistedRawSource.coloredTuple
    split_ifs <;> ring
  unfold TwistedRawSource.coloredTuple at hh
  rw [hh]
  ring

end
end QRH.Cycle092.RegularColoredForward

#print axioms QRH.Cycle092.RegularColoredForward.frame_original_masked_row_eq
