/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Full-source common sector projection for two independently colored columns.
   This extends the finite native allocation/regrouping argument; the carrier
   is the original sourceColumns, so no cancellation-dependent S0 is used. -/
import Candidate.C092.transport.TwistedRawSourceMasked
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawSource
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentFirstSectors
open CenteredMomentCommonAllocationSum CenteredMomentSecondSectorColumns CenteredMomentSourceRow
open CenteredMomentLiveDomain CenteredMomentSourceRectangle
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance (priority := 2000) sumCommonDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _

def projectedColumn (r : Source ι a b) (ω₁ ω₂ : Id →*₀ ℂ)
    (ν : ι → Id → ℂ) (W₁ W₂ : ℝ → ℂ) : Id → ℂ :=
  coloredColumn (Fintype.piFinset (MixedPrincipalAllocations.tuplePools r))
    (MixedCommonRestriction.punctureProduct r.S r.H) ω₁ ω₂
    (profileCoefficient r.R ν r.Wslot r.P W₁ W₂ r.X₁ r.X₂ r.Y₁ r.Y₂ r.d.1 r.d.2 1)

def commonMaskedRow (r : Source ι a b) (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (G L : Id) (ν : ι → Id → ℂ) (W₁ W₂ : ℝ → ℂ) : ℂ :=
  ∑ B : actualAllocations (MixedPrincipalAllocations.tuplePools r) G,
    (MixedCommonCoefficient.frozenWeight (MixedCommonRestriction.punctureProduct r.S r.H) B.val *
      ordinaryColor ω₁ ω₂ B.val * frozenCoefficient B.val G r.R ν r.Wslot r.P) *
      MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P *
      maskedLiveSum ω₁ ω₂ χ r.S r.H r.pool r.d r.hd B.val
        (allocation_data _ G B.val (Finset.mem_filter.mp B.property).1).1
        G r.R L ν r.Wslot r.P W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂

/-- Full original source carrier; independent colors can undo old aggregate
    cancellation, so the old uncolored active set cannot be substituted. -/
theorem sector_projectedColumn_eq_commonMaskedRow (r : Source ι a b)
    (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character) (hχ : ∀ I : Id, ¬Supported I → idealCoeff χ I = 0)
    (G : Id) (hG : Supported G) (L : Id) (ν : ι → Id → ℂ) (W₁ W₂ : ℝ → ℂ) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P *
      (∑ I : sectorPool G hG.1 (sourceColumns r),
        (if L ∣ (I:Id) then projectedColumn r ω₁ ω₂ ν W₁ W₂ (G*I) else 0) * idealCoeff χ I) =
      commonMaskedRow r ω₁ ω₂ χ G L ν W₁ W₂ := by
  let S := MixedPrincipalAllocations.tuplePools r
  let H := MixedCommonRestriction.punctureProduct r.S r.H
  let Q := residualPool G hG.1 (sourceColumns r)
  let f (I : Id) : ℂ := if L ∣ I then idealCoeff χ I else 0
  let c (B : actualAllocations S G) : ℂ :=
    MixedCommonCoefficient.frozenWeight H B.val * ordinaryColor ω₁ ω₂ B.val *
      frozenCoefficient B.val G r.R ν r.Wslot r.P
  let d (B : actualAllocations S G) (I : Id) : ℂ :=
    coloredColumn (liveBox S B.val (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1)
      H ω₁ ω₂ (liveProfile B.val G r.R ν r.Wslot r.P W₁ W₂
        r.X₁ r.X₂ r.Y₁ r.Y₂ r.d.1 r.d.2) I
  have hS : ∀ j, ∀ I ∈ S j, I ≠ 0 :=
    MixedLiteralAllocation.source_pools_nonzero r.pool r.hp r.d r.hd b r.X₁ r.X₂ r.Y₁ r.Y₂
  have hp : ∀ i, ∀ I ∈ S (Sum.inl i), Prime I := r.hp
  have hcols : sourceColumns r = finiteColumns (Fintype.piFinset S) := rfl
  have hQ (I : Id) (hI : I ∈ Q) : I ≠ 0 := by
    have hm := (mem_residualPool G hG.1 _ I).mp hI
    rw [hcols] at hm
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hm
    have hz : finiteTupleProduct v ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => hS j _ (Fintype.mem_piFinset.mp hv j))
    exact right_ne_zero_of_mul (he ▸ hz)
  have hsupport (B : actualAllocations S G) (I : Id) (hne : d B I ≠ 0) :
      G*I ∈ finiteColumns (Fintype.piFinset S) ∧ I ≠ 0 ∧ IsCoprime G I := by
    exact MixedCommonEnergy.masked_live_support S hS hp B.val
      (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1 G r.R I
      (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2 ν r.Wslot r.P
      W₁ W₂ r.X₁ r.X₂ r.Y₁ r.Y₂ r.d.1 r.d.2
      (fun v => MixedCommonCoefficient.tupleWeight H v * ordinaryColor ω₁ ω₂ v) hne
  have hexpand (I : Id) (hI : I ∈ Q) :
      (if IsCoprime G I then projectedColumn r ω₁ ω₂ ν W₁ W₂ (G*I) else 0) = ∑ B, c B*d B I := by
    by_cases hcop : IsCoprime G I
    · rw [ite_eq_left hcop]
      exact colored_column_allocations H S hS hp G r.R 1 I hG.1 (hQ I hI) hcop
        (one_dvd _) ω₁ ω₂ ν r.Wslot r.P W₁ W₂ r.X₁ r.X₂ r.Y₁ r.Y₂ r.d.1 r.d.2
    · rw [ite_eq_right hcop]
      symm
      apply Finset.sum_eq_zero
      intro B hB
      have hz : d B I = 0 := by
        by_contra hn
        exact hcop (hsupport B I hn).2.2
      rw [hz, mul_zero]
  have hsector : (∑ I : sectorPool G hG.1 (sourceColumns r),
      (if L ∣ (I:Id) then projectedColumn r ω₁ ω₂ ν W₁ W₂ (G*I) else 0)*idealCoeff χ I) =
      ∑ I ∈ Q, (if IsCoprime G I then projectedColumn r ω₁ ω₂ ν W₁ W₂ (G*I) else 0)*f I := by
    rw [Finset.sum_coe_sort (sectorPool G hG.1 (sourceColumns r))
      (fun I : Id => (if L ∣ I then projectedColumn r ω₁ ω₂ ν W₁ W₂ (G*I) else 0)*idealCoeff χ I)]
    unfold sectorPool
    rw [← supported_residualPool G hG, Finset.sum_filter]
    unfold supportedColumns
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro I hI
    by_cases hs : Supported I
    · by_cases hc : IsCoprime G I <;> by_cases hl : L ∣ I <;>
        simp only [hs, hc, hl, ite_true, ite_false, f, mul_zero, zero_mul]
    · simp only [hs, ite_false, hχ I hs, f]
      split_ifs <;> ring
  rw [hsector]
  have hsum : (∑ I ∈ Q, (if IsCoprime G I then projectedColumn r ω₁ ω₂ ν W₁ W₂ (G*I) else 0)*f I) =
      ∑ B : actualAllocations S G, c B * maskedLiveSum ω₁ ω₂ χ r.S r.H r.pool r.d r.hd
        B.val (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1
        G r.R L ν r.Wslot r.P W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂ := by
    simp_rw [Finset.sum_congr rfl (fun I hI => congrArg (fun z : ℂ => z*f I) (hexpand I hI)), Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro B hB
    simp only [mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    have he := sum_same_support Q
      (finiteColumns (liveBox S B.val (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1))
      (d B) f (fun I _ hn => finite_column_mem _ _ I hn) (by
        intro I _ hn
        apply (mem_residualPool G hG.1 _ I).mpr
        rw [hcols]
        exact (hsupport B I hn).1)
    rw [he]
    unfold d coloredColumn
    rw [finite_column_regroup]
    unfold maskedLiveSum
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [f, H, S, coloredTuple]
    split_ifs <;> ring
  rw [hsum, Finset.mul_sum]
  unfold commonMaskedRow
  apply Finset.sum_congr rfl
  intro B hB
  dsimp only [c, H, S]
  ring

#print axioms sector_projectedColumn_eq_commonMaskedRow
end
end QRH.Cycle092.TwistedRawSource
