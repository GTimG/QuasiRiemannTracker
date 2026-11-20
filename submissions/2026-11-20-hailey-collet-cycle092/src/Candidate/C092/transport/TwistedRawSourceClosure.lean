/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The full colored common/primary source projection, before norms. -/
import Candidate.C092.transport.TwistedRawSourceCommon
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawSource
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentSourceLiveColumn CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation CenteredMomentSecondSectorColumns
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance (priority := 2000) sumClosureDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _

def commonAllocations (r : Source ι a b) (G : Id) :=
  actualAllocations (MixedPrincipalAllocations.tuplePools r) G

def commonD (r : Source ι a b) (G : Id) (B : commonAllocations r G) : Id × Id :=
  (r.d.1*B.val (Sum.inr 0), r.d.2*B.val (Sum.inr 1))

theorem commonD_ne (r : Source ι a b) (G : Id) (B : commonAllocations r G) :
    (commonD r G B).1 ≠ 0 ∧ (commonD r G B).2 ≠ 0 := by
  have hB := (allocation_data _ G B.val (Finset.mem_filter.mp B.property).1).1
  exact ⟨mul_ne_zero r.hd.1 (hB _),mul_ne_zero r.hd.2 (hB _)⟩

def primaryAllocations (r : Source ι a b) (G : Id) (B : commonAllocations r G) (L : Id) :=
  MixedFixedSupport.boundedLabels
    (MixedLiteralAllocation.sourcePools (fun i : liveIndices B.val => r.pool i.val)
      (commonD r G B) (commonD_ne r G B) b r.X₁ r.X₂ r.Y₁ r.Y₂) L

def primaryCanonicalSource (r : Source ι a b) (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (G L : Id) (B : commonAllocations r G) (E : primaryAllocations r G B L)
    (ν : ι → Id → ℂ) (W₁ W₂ : ℝ → ℂ) : ℂ :=
  canonicalSource ω₁ ω₂ χ r.S r.H ((r.R*G)*L)
    (fun i : liveIndices E.val => r.pool i.val.val)
    (fun i => ν i.val.val) (fun i => r.Wslot i.val.val) (fun i => r.P i.val.val)
    W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂
    ((commonD r G B).1*E.val (Sum.inr 0),(commonD r G B).2*E.val (Sum.inr 1))

def primaryCanonicalScalar (r : Source ι a b) (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (G L : Id) (B : commonAllocations r G) (E : primaryAllocations r G B L)
    (ν : ι → Id → ℂ)
    (aL : Allocation L (Finset.univ : Finset (liveIndices B.val ⊕ Fin 2))) : ℂ :=
  MixedCommonCoefficient.frozenWeight (MixedCommonRestriction.punctureProduct r.S r.H) E.val *
    ordinaryColor ω₁ ω₂ E.val * allocationTerm L Finset.univ E.val aL *
    idealCoeff χ (finiteTupleProduct E.val) *
    (MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i : liveIndices B.val => r.P i.val) *
      frozenCoefficient E.val (finiteTupleProduct E.val) (r.R*G)
        (fun i : liveIndices B.val => ν i.val) (fun i => r.Wslot i.val) (fun i => r.P i.val))

def fullPrimaryRow (r : Source ι a b) (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (G L : Id) (B : commonAllocations r G) (ν : ι → Id → ℂ) (W₁ W₂ : ℝ → ℂ)
    (aL : Allocation L (Finset.univ : Finset (liveIndices B.val ⊕ Fin 2))) : ℂ :=
  ∑ E : primaryAllocations r G B L,
    primaryCanonicalScalar r ω₁ ω₂ χ G L B E ν aL *
      primaryCanonicalSource r ω₁ ω₂ χ G L B E ν W₁ W₂

theorem common_live_full_primary_identity (r : Source ι a b) (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (G L : Id) (hL : Squarefree L) (B : commonAllocations r G)
    (ν : ι → Id → ℂ) (W₁ W₂ : ℝ → ℂ) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i : liveIndices B.val => r.P i.val) *
      maskedLiveSum ω₁ ω₂ χ r.S r.H r.pool r.d r.hd B.val
        (allocation_data _ G B.val (Finset.mem_filter.mp B.property).1).1
        G r.R L ν r.Wslot r.P W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂ =
      ∑ aL : Allocation L (Finset.univ : Finset (liveIndices B.val ⊕ Fin 2)),
        fullPrimaryRow r ω₁ ω₂ χ G L B ν W₁ W₂ aL := by
  rw [masked_live_sum ω₁ ω₂ χ r.S r.H r.pool r.d r.hd B.val
    (allocation_data _ G B.val (Finset.mem_filter.mp B.property).1).1 G r.R L hL
    ν r.Wslot r.P W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂]
  apply Finset.sum_congr rfl
  intro aL haL
  have hh := allocated_row_canonical ω₁ ω₂ χ r.S r.H (fun i : liveIndices B.val => r.pool i.val)
    (fun i I hI => r.hp i.val I hI) (commonD r G B) (commonD_ne r G B)
    L L (r.R*G) hL.ne_zero (dvd_refl L) aL (fun i => ν i.val)
    (fun i => r.Wslot i.val) (fun i => r.P i.val) W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂
  unfold fullPrimaryRow primaryCanonicalScalar primaryCanonicalSource primaryAllocations
  exact hh.trans (by
    apply Finset.sum_congr rfl
    intro E hE
    ring)

theorem live_normalization_ne (r : Source ι a b) (G : Id) (B : commonAllocations r G) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i : liveIndices B.val => r.P i.val) ≠ 0 := by
  unfold MixedLiveNormalization.normalization
  apply mul_ne_zero
  · exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (mul_pos (r.hL.trans_le r.hX₁) (r.hL.trans_le r.hX₂))).ne')
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (zero_lt_one.trans_le (r.hP i.val))).ne'))

def fullyAllocatedCommonRow (r : Source ι a b) (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (G L : Id) (ν : ι → Id → ℂ) (W₁ W₂ : ℝ → ℂ) : ℂ :=
  ∑ B : commonAllocations r G,
    (MixedCommonCoefficient.frozenWeight (MixedCommonRestriction.punctureProduct r.S r.H) B.val *
      ordinaryColor ω₁ ω₂ B.val * frozenCoefficient B.val G r.R ν r.Wslot r.P) *
      (MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P *
        (MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i : liveIndices B.val => r.P i.val))⁻¹) *
      ∑ aL : Allocation L (Finset.univ : Finset (liveIndices B.val ⊕ Fin 2)),
        fullPrimaryRow r ω₁ ω₂ χ G L B ν W₁ W₂ aL

theorem commonMaskedRow_eq_fullyAllocated (r : Source ι a b) (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (G L : Id) (hL : Squarefree L) (ν : ι → Id → ℂ) (W₁ W₂ : ℝ → ℂ) :
    commonMaskedRow r ω₁ ω₂ χ G L ν W₁ W₂ =
      fullyAllocatedCommonRow r ω₁ ω₂ χ G L ν W₁ W₂ := by
  unfold commonMaskedRow fullyAllocatedCommonRow
  apply Finset.sum_congr rfl
  intro B hB
  have hh := common_live_full_primary_identity r ω₁ ω₂ χ G L hL B ν W₁ W₂
  have he := congrArg (fun z : ℂ =>
    (MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i : liveIndices B.val => r.P i.val))⁻¹*z) hh
  rw [← mul_assoc, inv_mul_cancel₀ (live_normalization_ne r G B), one_mul] at he
  rw [he]
  ring

/-- Complete native colored common-sector projection to the actual canonical
    source. Both ordinary prefix colors and the exact N/Nlive are explicit. -/
theorem sector_projectedColumn_eq_fullyAllocated (r : Source ι a b) (ω₁ ω₂ : Id →*₀ ℂ)
    (χ : Character) (hχ : ∀ I : Id, ¬Supported I → idealCoeff χ I = 0)
    (G : Id) (hG : Supported G) (L : Id) (hL : Squarefree L)
    (ν : ι → Id → ℂ) (W₁ W₂ : ℝ → ℂ) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P *
      (∑ I : sectorPool G hG.1 (sourceColumns r),
        (if L ∣ (I:Id) then projectedColumn r ω₁ ω₂ ν W₁ W₂ (G*I) else 0)*idealCoeff χ I) =
      fullyAllocatedCommonRow r ω₁ ω₂ χ G L ν W₁ W₂ := by
  exact (sector_projectedColumn_eq_commonMaskedRow r ω₁ ω₂ χ hχ G hG L ν W₁ W₂).trans
    (commonMaskedRow_eq_fullyAllocated r ω₁ ω₂ χ G L hL ν W₁ W₂)

#print axioms common_live_full_primary_identity
#print axioms commonMaskedRow_eq_fullyAllocated
#print axioms sector_projectedColumn_eq_fullyAllocated
end
end QRH.Cycle092.TwistedRawSource
