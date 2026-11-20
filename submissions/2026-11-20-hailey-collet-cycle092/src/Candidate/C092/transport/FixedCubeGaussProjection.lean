/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Native finite source projection, retaining the signed rectangle. -/
import Candidate.C092.transport.FixedCubeGaussCommon
import Candidate.C092.transport.FixedCubeGaussFourier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSecondSectorColumns
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentLattice
open CenteredMomentLiveDomain CenteredMomentSourceRectangle
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedHeightEnergy MixedCommonRestriction MixedCommonCoefficient
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def projectedColumn (r : Source ι a b) (ν : ι→Id→ℂ) (W₁ W₂ : ℝ→ℂ) (I : Id) : ℂ :=
  finiteColumnCoefficient (Fintype.piFinset (sourcePools r))
    (fun v=>tupleWeight (punctureProduct r.S r.H) v*
      profileCoefficient r.R ν r.Wslot r.P W₁ W₂
        r.X₁ r.X₂ r.Y₁ r.Y₂ r.d.1 r.d.2 1 v) I

/-- The actual common/divisor source projection, with arbitrary profile
heights. The ordinary signed rectangle remains inside the native profile. -/
theorem sector_projectedColumn_eq_commonMaskedRow (r : Source ι a b)
    (χ : Character) (hχ : ∀I:Id,¬Supported I → idealCoeff χ I=0)
    (G : Id) (hG : Supported G) (L : Id) (ν : ι→Id→ℂ) (W₁ W₂ : ℝ→ℂ) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      (∑ I : sectorPool G hG.1 (sourceColumns r),
        (if L∣(I:Id) then projectedColumn r ν W₁ W₂ (G*I) else 0)*idealCoeff χ I)=
      MixedCommonSource.commonMaskedRow χ r.S r.H r.pool r.d r.hd G r.R L ν r.Wslot r.P
        W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂ := by
  have hdec : (MixedPrincipalWindow.instDecidableEqSumFinOfNatNat_submissions : DecidableEq (ι⊕Fin 2))=
      (inferInstance : DecidableEq (ι⊕Fin 2)) := Subsingleton.elim _ _
  have hdecE : (MixedCommonEnergy.instDecidableEqSumFinOfNatNat_submissions : DecidableEq (ι⊕Fin 2))=
      (inferInstance : DecidableEq (ι⊕Fin 2)) := Subsingleton.elim _ _
  have hcols : sourceColumns r=finiteColumns (Fintype.piFinset (sourcePools r)) := by
    unfold sourceColumns sourcePools
    rw [hdec]
  let S := sourcePools r
  let Q := residualPool G hG.1 (sourceColumns r)
  let f (I : Id) : ℂ := if L∣I then idealCoeff χ I else 0
  let c (B : actualAllocations S G) : ℂ :=
    frozenWeight (punctureProduct r.S r.H) B.val*frozenCoefficient B.val G r.R ν r.Wslot r.P
  let d (B : actualAllocations S G) (I : Id) : ℂ :=
    finiteColumnCoefficient (liveBox S B.val (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1)
      (fun v=>tupleWeight (punctureProduct r.S r.H) v*
        liveProfile B.val G r.R ν r.Wslot r.P W₁ W₂ r.X₁ r.X₂ r.Y₁ r.Y₂ r.d.1 r.d.2 v) I
  have hS : ∀j,∀I∈S j,I≠0 :=
    MixedLiteralAllocation.source_pools_nonzero r.pool r.hp r.d r.hd b r.X₁ r.X₂ r.Y₁ r.Y₂
  have hp : ∀i,∀I∈S (Sum.inl i),Prime I := r.hp
  have hQ (I : Id) (hI : I∈Q) : I≠0 := by
    have hm := (mem_residualPool G hG.1 _ I).mp hI
    rw [hcols] at hm
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hm
    have hz : finiteTupleProduct v≠0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _=>hS j _ (Fintype.mem_piFinset.mp hv j))
    exact right_ne_zero_of_mul (he ▸ hz)
  have hexpand (I : Id) (hI : I∈Q) :
      (if IsCoprime G I then projectedColumn r ν W₁ W₂ (G*I) else 0)=∑B,c B*d B I := by
    have hh := MixedCommonEnergy.punctured_restricted_column (punctureProduct r.S r.H) S hS hp
      G r.R 1 I hG.1 (hQ I hI) (one_dvd G) ν r.Wslot r.P W₁ W₂
      r.X₁ r.X₂ r.Y₁ r.Y₂ r.d.1 r.d.2
    rw [hdecE] at hh
    simpa only [projectedColumn,c,d,S] using hh
  have hsector : (∑I : sectorPool G hG.1 (sourceColumns r),
      (if L∣(I:Id) then projectedColumn r ν W₁ W₂ (G*I) else 0)*idealCoeff χ I)=
      ∑I∈Q,(if IsCoprime G I then projectedColumn r ν W₁ W₂ (G*I) else 0)*f I := by
    rw [Finset.sum_coe_sort (sectorPool G hG.1 (sourceColumns r))
      (fun I:Id=>(if L∣I then projectedColumn r ν W₁ W₂ (G*I) else 0)*idealCoeff χ I)]
    unfold sectorPool
    rw [←supported_residualPool G hG,Finset.sum_filter]
    unfold supportedColumns
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro I hI
    by_cases hs : Supported I
    · by_cases hc : IsCoprime G I <;> by_cases hl : L∣I <;>
        simp only [hs,hc,hl,ite_true,ite_false,f,mul_zero,zero_mul]
    · simp only [hs,ite_false,hχ I hs,f]
      split_ifs <;> ring
  rw [hsector]
  have hsum : (∑I∈Q,(if IsCoprime G I then projectedColumn r ν W₁ W₂ (G*I) else 0)*f I)=
      ∑B : actualAllocations S G,c B*MixedDivisorMask.maskedLiveSum χ r.S r.H r.pool r.d r.hd
        B.val (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1
        G r.R L ν r.Wslot r.P W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂ := by
    simp_rw [Finset.sum_congr rfl (fun I hI=>congrArg (fun z:ℂ=>z*f I) (hexpand I hI)),Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro B _
    simp only [mul_assoc]
    rw [←Finset.mul_sum]
    congr 1
    have he := sum_same_support Q
      (finiteColumns (liveBox S B.val (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1))
      (d B) f (fun I _ hn=>finite_column_mem _ _ I hn) (by
        intro I _ hn
        have hm := MixedCommonEnergy.masked_live_support S hS hp B.val
          (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1 G r.R I
          (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
          ν r.Wslot r.P W₁ W₂ r.X₁ r.X₂ r.Y₁ r.Y₂ r.d.1 r.d.2
          (tupleWeight (punctureProduct r.S r.H)) hn
        rw [hdecE] at hm
        apply (mem_residualPool G hG.1 _ I).mpr
        rw [hcols]
        exact hm.1)
    rw [he]
    unfold d
    rw [finite_column_regroup]
    unfold MixedDivisorMask.maskedLiveSum
    apply Finset.sum_congr rfl
    intro v _
    dsimp only [f]
    split_ifs <;> ring
  rw [hsum,Finset.mul_sum]
  unfold MixedCommonSource.commonMaskedRow
  apply Finset.sum_congr rfl
  intro B _
  dsimp only [c]
  ring

#print axioms sector_projectedColumn_eq_commonMaskedRow
end
end QRH.Cycle092.FixedCubeGauss
