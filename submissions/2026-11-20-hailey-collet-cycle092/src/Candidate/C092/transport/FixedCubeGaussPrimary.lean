/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Both allocations use the pinned original native projectors. -/
import Candidate.C092.transport.FixedCubeGaussProjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentCommonProfile CenteredMomentDivisorAllocation CenteredMomentSourceRow
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedCommonRestriction MixedCommonCoefficient
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance c092LocalInst_Candidate_C092_transport_FixedCubeGaussPrimary_ce2c3b2823b3a551_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def commonLivePool (r : Source ι a b) (G : Id) (B : commonAlloc r G) : liveIndices B.val→Finset Id :=
  fun i=>r.pool i.val

def commonLiveD (r : Source ι a b) (G : Id) (B : commonAlloc r G) : Id×Id :=
  (r.d.1*B.val (Sum.inr 0),r.d.2*B.val (Sum.inr 1))

theorem commonLiveD_ne (r : Source ι a b) (G : Id) (B : commonAlloc r G) :
    (commonLiveD r G B).1≠0 ∧ (commonLiveD r G B).2≠0 :=
  ⟨mul_ne_zero r.hd.1 (commonAlloc_ne r G B _),mul_ne_zero r.hd.2 (commonAlloc_ne r G B _)⟩

def primaryPools (r : Source ι a b) (G : Id) (B : commonAlloc r G) :=
  MixedLiteralAllocation.sourcePools (commonLivePool r G B) (commonLiveD r G B) (commonLiveD_ne r G B)
    b r.X₁ r.X₂ r.Y₁ r.Y₂

def fullPrimaryAlloc (r : Source ι a b) (G : Id) (B : commonAlloc r G) (L : Id) :=
  MixedFixedSupport.boundedLabels (primaryPools r G B) L

theorem fullPrimaryAlloc_ne (r : Source ι a b) (G : Id) (B : commonAlloc r G) (L : Id)
    (E : fullPrimaryAlloc r G B L) : ∀j,E.val j≠0 :=
  (allocation_data _ _ E.val (Finset.mem_filter.mp E.property).1).1

/-- The whole L-primary parts occur in E. `allocationTerm` retains the signed
nonempty-subset allocation; no condition L divides the conductor is inserted. -/
def fullPrimaryRow (r : Source ι a b) (χ : Character) (G L : Id) (B : commonAlloc r G)
    (ν : ι→Id→ℂ) (W₁ W₂ : ℝ→ℂ)
    (aL : Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2))) : ℂ :=
  ∑ E : fullPrimaryAlloc r G B L,
    frozenWeight (punctureProduct r.S r.H) E.val*
      allocationTerm L Finset.univ E.val aL*idealCoeff χ (finiteTupleProduct E.val)*
      MixedAllocationSource.frozenRow χ r.S r.H (commonLivePool r G B)
        (commonLiveD r G B) (commonLiveD_ne r G B) E.val (fullPrimaryAlloc_ne r G B L E)
        L (r.R*G) (fun i=>ν i.val) (fun i=>r.Wslot i.val) (fun i=>r.P i.val)
        W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂

/-- Exact simultaneous common-G and full second-divisor primary allocation.
The left side is Sil's actual common residual source, with its actual live
normalization. It keeps the entire signed equal-product rectangle. -/
theorem common_live_full_primary_identity (r : Source ι a b) (χ : Character)
    (G L : Id) (hL : Squarefree L) (B : commonAlloc r G)
    (ν : ι→Id→ℂ) (W₁ W₂ : ℝ→ℂ) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i:liveIndices B.val=>r.P i.val)*
      MixedDivisorMask.maskedLiveSum χ r.S r.H r.pool r.d r.hd B.val (commonAlloc_ne r G B)
        G r.R L ν r.Wslot r.P W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂=
      ∑aL : Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)),
        fullPrimaryRow r χ G L B ν W₁ W₂ aL := by
  rw [MixedDivisorMask.masked_live_sum χ r.S r.H r.pool r.d r.hd B.val (commonAlloc_ne r G B)
    G r.R L hL ν r.Wslot r.P W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro aL _
  have hh := MixedCommonAllocated.allocated_live_row χ r.S r.H r.pool r.d r.hd B.val
    (commonAlloc_ne r G B) G r.R L aL ν r.Wslot r.P W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂
  have he := MixedLiteralAllocation.allocated_row_identity χ r.S r.H (commonLivePool r G B)
    (fun i I hI=>r.hp i.val I hI) (commonLiveD r G B) (commonLiveD_ne r G B)
    L L (r.R*G) hL.ne_zero (dvd_refl L) aL (fun i=>ν i.val)
    (fun i=>r.Wslot i.val) (fun i=>r.P i.val) W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂
  unfold fullPrimaryRow fullPrimaryAlloc primaryPools
  exact hh.trans he

theorem live_normalization_ne (r : Source ι a b) (G : Id) (B : commonAlloc r G) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i:liveIndices B.val=>r.P i.val)≠0 := by
  unfold MixedLiveNormalization.normalization
  apply mul_ne_zero
  · exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (mul_pos (r.hL.trans_le r.hX₁) (r.hL.trans_le r.hX₂))).ne')
  · exact Finset.prod_ne_zero_iff.mpr (fun i _=>inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (zero_lt_one.trans_le (r.hP i.val))).ne'))

theorem common_live_full_primary_inverse (r : Source ι a b) (χ : Character)
    (G L : Id) (hL : Squarefree L) (B : commonAlloc r G)
    (ν : ι→Id→ℂ) (W₁ W₂ : ℝ→ℂ) :
    MixedDivisorMask.maskedLiveSum χ r.S r.H r.pool r.d r.hd B.val (commonAlloc_ne r G B)
      G r.R L ν r.Wslot r.P W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂=
      (MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i:liveIndices B.val=>r.P i.val))⁻¹*
        ∑aL : Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)),
          fullPrimaryRow r χ G L B ν W₁ W₂ aL := by
  rw [←common_live_full_primary_identity r χ G L hL B ν W₁ W₂,←mul_assoc,
    inv_mul_cancel₀ (live_normalization_ne r G B),one_mul]

/-- Explicit global native projection, exposing every full G allocation,
every signed L allocation, every entire L-primary tuple, and the exact
normalization ratio. -/
def fullyAllocatedCommonRow (r : Source ι a b) (χ : Character) (G L : Id)
    (ν : ι→Id→ℂ) (W₁ W₂ : ℝ→ℂ) : ℂ :=
  ∑B : commonAlloc r G,
    (frozenWeight (punctureProduct r.S r.H) B.val*frozenCoefficient B.val G r.R ν r.Wslot r.P)*
      (MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
        (MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i:liveIndices B.val=>r.P i.val))⁻¹)*
        ∑aL : Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)),
          fullPrimaryRow r χ G L B ν W₁ W₂ aL

theorem commonMaskedRow_eq_fullyAllocated (r : Source ι a b) (χ : Character)
    (G L : Id) (hL : Squarefree L) (ν : ι→Id→ℂ) (W₁ W₂ : ℝ→ℂ) :
    MixedCommonSource.commonMaskedRow χ r.S r.H r.pool r.d r.hd G r.R L ν r.Wslot r.P
      W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂=fullyAllocatedCommonRow r χ G L ν W₁ W₂ := by
  unfold MixedCommonSource.commonMaskedRow fullyAllocatedCommonRow
  apply Finset.sum_congr rfl
  intro B _
  rw [common_live_full_primary_inverse r χ G L hL B ν W₁ W₂]
  ring

#print axioms common_live_full_primary_identity
#print axioms commonMaskedRow_eq_fullyAllocated
end
end QRH.Cycle092.FixedCubeGauss
