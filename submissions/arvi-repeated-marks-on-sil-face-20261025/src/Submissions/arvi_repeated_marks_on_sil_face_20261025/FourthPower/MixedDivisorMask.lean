/- Copyright (c) 2026 Sil. Apache-2.0.
Sum artificial allocations back to the literal divisibility mask.
Their selected-product norms retain the whole squarefree divisor.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedCommonAllocated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedDivisorMask
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorEnergy
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open MixedCommonAllocated MixedLiteralAllocation MixedCommonCoefficient MixedCommonRestriction
local notation "Id" => Ideal HeckeFamily.O

theorem squarefree_dvd_selected_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Id) (hD : Squarefree D) (a : Allocation D (Finset.univ : Finset ι)) :
    D∣∏i,selectedDivisor D Finset.univ a i := by
  apply (squarefree_dvd_iff _ _ hD).mpr
  intro P hP
  let p : IdealMobiusDivisorSum.primeSupport D := ⟨P,hP⟩
  have hn : (a p).val.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp (a p).property).1
  obtain ⟨i,hi⟩ := hn
  have hpi : p∈selectedPrimes D Finset.univ a i :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ p,hi⟩
  exact (Finset.dvd_prod_of_mem (fun q : IdealMobiusDivisorSum.primeSupport D=>(q:Id)) hpi).trans
    (Finset.dvd_prod_of_mem (fun i=>selectedDivisor D Finset.univ a i) (Finset.mem_univ i))

theorem squarefree_norm_le_selected_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Id) (hD : Squarefree D) (a : Allocation D (Finset.univ : Finset ι)) :
    (D.absNorm:ℝ)≤(∏i,selectedDivisor D Finset.univ a i).absNorm :=
  CenteredExceptionalCount.norm_le_of_dvd
    (Finset.prod_ne_zero_iff.mpr (fun i _=>selectedDivisor_ne_zero D Finset.univ a i))
    (squarefree_dvd_selected_product D hD a)

/-- The constant is independent of the index type, given its dimension
cap. Thus it also precedes any genuine common allocation. -/
theorem allocation_count_squared (N : ℕ) (hN : 0<N) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι] [DecidableEq ι],Fintype.card ι≤N →
    ∀D : Id,D≠0 → (Fintype.card (Allocation D (Finset.univ : Finset ι)):ℝ)^2≤C*(D.absNorm:ℝ)^ε := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  obtain ⟨C,hC,hbase⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/(2*N)) (div_pos hε (by positivity))
  refine ⟨C^(2*N),pow_pos hC _,?_⟩
  intro ι _ _ hn D hD
  have hc : (Fintype.card (Allocation D (Finset.univ : Finset ι)):ℝ)≤
      ((2:ℝ)^(IdealMobiusDivisorSum.primeSupport D).card)^Fintype.card ι := by
    exact_mod_cast allocation_card_bound D (Finset.univ : Finset ι)
  calc
    _ ≤ (((2:ℝ)^(IdealMobiusDivisorSum.primeSupport D).card)^Fintype.card ι)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
    _ ≤ (((2:ℝ)^(IdealMobiusDivisorSum.primeSupport D).card)^N)^2 :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hn) 2
    _ = ((2:ℝ)^(IdealMobiusDivisorSum.primeSupport D).card)^(2*N) := by
      rw [←pow_mul,Nat.mul_comm N 2]
    _ ≤ (C*(D.absNorm:ℝ)^(ε/(2*N)))^(2*N) :=
      pow_le_pow_left₀ (by positivity) (hbase D hD) _
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _)]
      congr 2
      push_cast
      field_simp

variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _

theorem selected_budget_bound (D : Id) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (Z κ : ℝ) (w : α→ℝ) (hZ : 1≤Z) (hκ : 0≤κ) (hw : ∀i,0≤w i) :
    Z^(κ*(∑i : selectedLive D a,w i.val))/((∏j,selectedDivisor D Finset.univ a j).absNorm:ℝ)≤
      Z^(κ*(∑i,w i))/(D.absNorm:ℝ) := by
  have hDpos : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  apply (div_le_div_of_nonneg_left (Real.rpow_nonneg (zero_le_one.trans hZ) _)
    hDpos (squarefree_norm_le_selected_product D hD a)).trans
  apply div_le_div_of_nonneg_right _ hDpos.le
  apply Real.rpow_le_rpow_of_exponent_le hZ
  apply mul_le_mul_of_nonneg_left _ hκ
  simpa only [Finset.sum_coe_sort] using Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (selectedLive D a)) (fun i _ _=>hw i)

def maskedLiveSum (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (B : Tuple α) (hB : ∀j,B j≠0) (G R D : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑v∈liveBox (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) B hB,
    if D∣finiteTupleProduct v then tupleWeight (punctureProduct S H) v*
      liveProfile B G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 v*
      idealCoeff χ (finiteTupleProduct v) else 0

theorem masked_live_sum (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (B : Tuple α) (hB : ∀j,B j≠0) (G R D : Id)
    (hD : Squarefree D) (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    maskedLiveSum χ S H pool d hd B hB G R D ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂=
      ∑a : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2)),
        allocatedLiveSum χ S H pool d hd B hB G R D a ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  have he := finite_mask_regroup D hD (Finset.univ : Finset (liveIndices B⊕Fin 2))
    (liveBox (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) B hB) id
    (fun (_ : Unit) v=>tupleWeight (punctureProduct S H) v*
      liveProfile B G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 v*
      idealCoeff χ (finiteTupleProduct v)) ()
  apply he.trans
  apply Finset.sum_congr rfl
  intro a ha
  unfold allocatedPolynomial allocatedLiveSum
  apply Finset.sum_congr rfl
  intro v hv
  dsimp only [id_eq]
  ring

end
end Candidate.FourthPower.MixedDivisorMask
