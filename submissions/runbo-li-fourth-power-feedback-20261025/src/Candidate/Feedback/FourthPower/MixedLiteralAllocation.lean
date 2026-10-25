/- Copyright (c) 2026 Sil. Apache-2.0.
Identify the original restricted, artificially allocated source with
the finite frozen-source family. No row or coefficient restriction is dropped.
-/
import Candidate.Feedback.FourthPower.MixedAllocationSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedLiteralAllocation
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentSourceMass CenteredMomentSourceRectangle CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentFirstSectors
open MixedTupleRows MixedCompletedRows MixedCommonCoefficient MixedCommonRestriction MixedFixedSupport
open MixedArtificialRestriction MixedFrozenSource MixedLiveNormalization MixedAllocationSource
open MixedAllocationCost MixedSourceAssembly
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _

def sourcePools (pool : α→Finset Id) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0)
    (b X₁ X₂ Y₁ Y₂ : ℝ) : (α⊕Fin 2)→Finset Id :=
  pools pool (residualPool d.1 hd.1 (plainSupportPool b X₁ Y₁))
    (residualPool d.2 hd.2 (plainSupportPool b X₂ Y₂))

omit [Fintype α] in
theorem source_pools_nonzero (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    ∀j,∀I∈sourcePools pool d hd b X₁ X₂ Y₁ Y₂ j,I≠0 := by
  have hplain (e : Id) (he : e≠0) (X Y : ℝ) (I : Id)
      (hI : I∈residualPool e he (plainSupportPool b X Y)) : I≠0 := by
    rw [residual_plain_pool] at hI
    rcases Finset.mem_union.mp hI with hI|hI
    · exact (mem_idealBall _ _ |>.mp hI).1
    · exact (mem_idealBall _ _ |>.mp hI).1
  intro j I hI
  cases j with
  | inl i => exact (hp i I hI).ne_zero
  | inr j =>
    fin_cases j
    · exact hplain d.1 hd.1 X₁ Y₁ I hI
    · exact hplain d.2 hd.2 X₂ Y₂ I hI

def allocatedRow (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (D R : Id)
    (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  normalization (X₁*X₂) P*
    ∑v∈Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂),
      tupleWeight (punctureProduct S H) v*allocationTerm D Finset.univ v a*
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v*
        idealCoeff χ (finiteTupleProduct v)

/-- The analytic family consists of the literal original source after
the already proved fixed-support expansion, with its signs intact. -/
theorem allocated_row_identity (χ : Character) (S H : Finset PrimeIdeal)
    (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (D F R : Id) (hF : F≠0) (hDF : D∣F)
    (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    allocatedRow χ S H pool d hd D R a ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂=
      ∑B : boundedLabels (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) F,
        (frozenWeight (punctureProduct S H) B.val*allocationTerm D Finset.univ B.val a*
          idealCoeff χ (finiteTupleProduct B.val))*
        frozenRow χ S H pool d hd B.val
          (allocation_data _ F B.val (Finset.mem_filter.mp B.property).1).1 F R
          ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  let T := sourcePools pool d hd b X₁ X₂ Y₁ Y₂
  have he := allocated_restricted_character_sum (punctureProduct S H) T
    (source_pools_nonzero pool hp d hd b X₁ X₂ Y₁ Y₂)
    (fun i I hI=>hp i I hI) D F R hF hDF a (idealCoeff χ).toMonoidHom
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2
  apply (congrArg (fun x : ℂ=>normalization (X₁*X₂) P*x) he).trans
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  unfold frozenRow liveSum
  dsimp only [T,sourcePools]
  have hψ (I : Id) : (idealCoeff χ).toMonoidHom I=idealCoeff χ I := rfl
  simp only [hψ]
  ring

theorem actual_phase_zero (H D : Id) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (B : Tuple α) (ha : allocationTerm D Finset.univ B a=0) (χ : Character) :
    frozenWeight H B*allocationTerm D Finset.univ B a*idealCoeff χ (finiteTupleProduct B)=0 := by
  rw [ha,mul_zero,zero_mul]

def selectedLive (D : Id) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) : Finset α :=
  Finset.univ.filter (fun i=>selectedDivisor D Finset.univ a (Sum.inl i)=1)

theorem actual_live_subset (D : Id) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (B : Tuple α) (ha : allocationTerm D Finset.univ B a≠0) :
    liveIndices B⊆selectedLive D a := by
  intro i hi
  have hb := (Finset.mem_filter.mp hi).2
  have hd := selectedDivisor_dvd D Finset.univ B a ha (Sum.inl i)
  rw [hb] at hd
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ i,?_⟩
  simpa only [Ideal.dvd_iff_le,Ideal.one_eq_top,top_le_iff] using hd

theorem selected_live_weight (D : Id) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (B : Tuple α) (hB : ∀j,B j≠0) (ha : allocationTerm D Finset.univ B a≠0)
    (Z κ : ℝ) (w : α→ℝ) (hZ : 1≤Z) (hκ : 0≤κ) (hw : ∀i,0≤w i) :
    liveWeight Z κ w B≤Z^(κ*(∑i : selectedLive D a,w i.val))/
      ((∏j,selectedDivisor D Finset.univ a j).absNorm:ℝ) := by
  apply (selected_weight D a B hB ha Z κ w (zero_le_one.trans hZ)).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  apply mul_le_mul_of_nonneg_left _ hκ
  simpa only [Finset.sum_coe_sort] using Finset.sum_le_sum_of_subset_of_nonneg
    (actual_live_subset D a B ha) (fun i _ _=>hw i)

/-- Fixed-support labels cost only a subpower, while the denominator
retains every selected divisor and the exponent uses only unforced slots. -/
theorem uniform_selected_budget (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : (α⊕Fin 2)→Finset Id)(F : Id),F≠0 →
    ∀D : Id,∀a : Allocation D (Finset.univ : Finset (α⊕Fin 2)),
    ∀(Z κ : ℝ)(w : α→ℝ),1≤Z → 0≤κ → (∀i,0≤w i) →
      budget (boundedLabels S F) (fun B=>allocationTerm D Finset.univ B.val a≠0) Z κ w≤
        C*(F.absNorm:ℝ)^ε*Z^(κ*(∑i : selectedLive D a,w i.val))/
          ((∏j,selectedDivisor D Finset.univ a j).absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := fixed_count_squared (ι:=α⊕Fin 2) ε hε
  refine ⟨C,hC,?_⟩
  intro S F hF D a Z κ w hZ hκ hw
  let E := Z^(κ*(∑i : selectedLive D a,w i.val))/
    ((∏j,selectedDivisor D Finset.univ a j).absNorm:ℝ)
  have hE : 0≤E := div_nonneg (Real.rpow_nonneg (zero_le_one.trans hZ) _) (Nat.cast_nonneg _)
  have hb : budget (boundedLabels S F) (fun B=>allocationTerm D Finset.univ B.val a≠0) Z κ w≤
      ((boundedLabels S F).card:ℝ)^2*E := by
    unfold budget
    calc
      _ ≤ ((boundedLabels S F).card:ℝ)*∑_B : boundedLabels S F,E := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro B hB
        split_ifs with hn
        · exact selected_live_weight D a B.val
            (allocation_data S F B.val (Finset.mem_filter.mp B.property).1).1 hn Z κ w hZ hκ hw
        · exact hE
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul];ring
  apply hb.trans
  apply (mul_le_mul_of_nonneg_right (hcount S F hF) hE).trans_eq
  dsimp only [E]
  ring

end
end Candidate.Feedback.FourthPower.MixedLiteralAllocation
