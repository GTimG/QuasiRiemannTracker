/- Copyright (c) 2026 Sil. Apache-2.0.
Complete actual finite rows using their zeros. Absorb an ordinary-only
puncture into the common character only when the marked coefficients
already vanish at those primes; no cancellation is discarded.
-/
import Candidate.SilPrior.FourthPower.MixedTupleRows
import Candidate.SilPrior.FourthPower.RestorationFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskExpansion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceRectangle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedCompletedRows
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelRowProfiles KernelRowExpansion
open KernelRowPools KernelRestrictedState KernelPunctureRows KernelLabelledSlots
open MixedCommonRestriction MixedTupleRows RestorationFamily
open CenteredMomentSourceMass CenteredMomentCommonMaskExpansion
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem active_pair_rectangle (χ : Character) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (n : Id×Id) (hn : pairCharacter χ n*pairProfile W₁ W₂ X₁ X₂ n≠0) :
    n∈rectangle b X₁ X₂ := by
  have hc := (mul_ne_zero_iff.mp hn).1
  have hp := (mul_ne_zero_iff.mp hn).2
  have hz : n.1≠0 ∧ n.2≠0 := by
    constructor
    · intro h;apply hc;simp only [pairCharacter,h,zero_mul,map_zero]
    · intro h;apply hc;simp only [pairCharacter,h,mul_zero,map_zero]
  have hw := mul_ne_zero_iff.mp hp
  exact Finset.mem_product.mpr ⟨(mem_idealBall _ _).mpr
    ⟨hz.1,(div_le_iff₀ hX₁).mp (hs₁ hw.1)⟩,(mem_idealBall _ _).mpr
    ⟨hz.2,(div_le_iff₀ hX₂).mp (hs₂ hw.2)⟩⟩

/-- A containing finite domain equals the canonical supported rectangle:
every omitted term is proved to be zero before taking any norm. -/
theorem normalized_row_complete (χ : Character) (S : Finset PrimeIdeal)
    (D : Finset (Id×Id)) (r : Id×Id→ℂ) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (hD : rectangle b X₁ X₂⊆D)
    (hoff : ∀I,¬Supported I→idealCoeff χ I=0)
    (hS : ∀I,Supported I→((I.absNorm:ℝ)≤b*X₁ ∨ (I.absNorm:ℝ)≤b*X₂)→
      primeSupport I⊆primeValues S) :
    normalizedRow χ D r W₁ W₂ X₁ X₂=
      normalizedRow χ (supportedRectangle S b X₁ X₂) r W₁ W₂ X₁ X₂ := by
  unfold normalizedRow
  apply congrArg (fun z : ℂ=>(Real.sqrt (X₁*X₂):ℂ)⁻¹*z)
  symm
  apply Finset.sum_subset ((Finset.filter_subset _ _).trans hD)
  intro n hn hnS
  by_contra hne
  have hc : pairCharacter χ n≠0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2
  have hp : pairCharacter χ n*pairProfile W₁ W₂ X₁ X₂ n≠0 :=
    mul_ne_zero hc (mul_ne_zero_iff.mp hne).2
  have hrect := active_pair_rectangle χ W₁ W₂ b X₁ X₂ hX₁ hX₂ hs₁ hs₂ n hp
  have hm : idealCoeff χ n.1≠0 ∧ idealCoeff χ n.2≠0 := by
    simpa only [pairCharacter,map_mul,mul_ne_zero_iff] using hc
  have hg : Supported n.1 ∧ Supported n.2 :=
    ⟨by by_contra hh;exact hm.1 (hoff _ hh),by by_contra hh;exact hm.2 (hoff _ hh)⟩
  have hb := Finset.mem_product.mp hrect
  apply hnS
  exact Finset.mem_filter.mpr ⟨hrect,Finset.union_subset
    (hS _ hg.1 (Or.inl ((mem_idealBall _ _).mp hb.1).2))
    (hS _ hg.2 (Or.inr ((mem_idealBall _ _).mp hb.2).2))⟩

def holes (H : Finset PrimeIdeal) : Finset Id := H.image Subtype.val

theorem holes_prime (H : Finset PrimeIdeal) : ∀I∈holes H,Prime I := by
  intro I hI
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hI
  exact Q.property

theorem mem_holes (H : Finset PrimeIdeal) (Q : PrimeIdeal) : Q.val∈holes H↔Q∈H := by
  simp only [holes,Finset.mem_image]
  constructor
  · rintro ⟨P,hP,hPQ⟩;exact Subtype.val_injective hPQ ▸ hP
  · intro h;exact ⟨Q,h,rfl⟩

theorem holes_product (H : Finset PrimeIdeal) : (∏I∈holes H,I)=∏P∈H,P.val := by
  rw [holes,Finset.prod_image]
  exact fun _ _ _ _ h=>Subtype.val_injective h

theorem ordinary_mask (S H : Finset PrimeIdeal) (hH : H⊆S) (live : S→Bool) (n : Id×Id) :
    restrictedValue S (augmented S H live) n=
      restrictedValue S live n*(if IsCoprime (n.1*n.2) (∏I∈holes H,I) then 1 else 0) := by
  have hc : IsCoprime (n.1*n.2) (∏I∈holes H,I)↔
      ∀P : S,P.val∈H→¬P.val.val∣n.1*n.2 := by
    rw [holes_product,IsCoprime.prod_right_iff]
    constructor
    · intro h P hP;exact (prime_coprime P.val _).mp (h P.val hP).symm
    · intro h P hP;exact ((prime_coprime P _).mpr (h ⟨P,hH hP⟩ hP)).symm
  unfold restrictedValue
  rw [augmented_restriction,hc]
  split_ifs <;> simp_all

theorem normalized_hole_absorption (χ : Character) (S H : Finset PrimeIdeal) (hH : H⊆S)
    (D : Finset (Id×Id)) (live : S→Bool) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ) :
    normalizedRow χ D (restrictedValue S (augmented S H live)) W₁ W₂ X₁ X₂=
      normalizedRow (χ.excludePrimes (holes H) (holes_prime H)) D
        (restrictedValue S live) W₁ W₂ X₁ X₂ := by
  unfold normalizedRow
  apply congrArg (fun z : ℂ=>(Real.sqrt (X₁*X₂):ℂ)⁻¹*z)
  apply Finset.sum_congr rfl
  intro n hn
  rw [ordinary_mask S H hH]
  unfold pairCharacter
  rw [←common_character_mask]
  ring

omit [Fintype ι] in
theorem natural_hole_absorption (χ : Character) (S H : Finset PrimeIdeal)
    (pool : ι→Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ)
    (hβ : ∀i,∀Q∈H,β i Q.val=0) :
    naturalCoefficients (χ.excludePrimes (holes H) (holes_prime H)) S pool β P=
      naturalCoefficients χ S pool β P := by
  funext i Q
  unfold naturalCoefficients slotTerm
  by_cases hp : Q.val.val∈pool i
  · rw [ite_eq_left hp,ite_eq_left hp,deleted_prime χ (holes H) (holes_prime H) Q.val.val Q.val.property]
    by_cases hQ : Q.val∈H
    · rw [ite_eq_left ((mem_holes H Q.val).mpr hQ),hβ i Q.val hQ]
      simp only [mul_zero]
    · rw [ite_eq_right (fun hh=>hQ ((mem_holes H Q.val).mp hh))]
  · rw [ite_eq_right hp,ite_eq_right hp]

theorem family_hole_absorption (χ : Character) (S H : Finset PrimeIdeal) (hH : H⊆S)
    (pool : ι→Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ)
    (hβ : ∀i,∀Q∈H,β i Q.val=0) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) :
    weightedSum (naturalCoefficients χ S pool β P)
      (fun slot=>normalizedRow χ (supportedRectangle S b X₁ X₂)
        (restrictedValue S (augmented S H (marked S slot))) W₁ W₂ X₁ X₂)=
      row false S (χ.excludePrimes (holes H) (holes_prime H)) pool β P W₁ W₂ b X₁ X₂ := by
  unfold row sourceValue
  simp only [Bool.false_eq_true,ite_false,natural_hole_absorption χ S H pool β P hβ]
  apply congrArg (weightedSum (naturalCoefficients χ S pool β P))
  funext slot
  exact normalized_hole_absorption χ S H hH _ _ W₁ W₂ X₁ X₂

theorem character_union (χ : Character) (R T : Finset Id)
    (hR : ∀I∈R,Prime I) (hT : ∀I∈T,Prime I) (I : Id) :
    idealCoeff ((χ.excludePrimes R hR).excludePrimes T hT) I=
      idealCoeff (χ.excludePrimes (R∪T) (fun J hJ=>(Finset.mem_union.mp hJ).elim (hR J) (hT J))) I := by
  have hu : (∀P∈R∪T,IsCoprime I P)↔(∀P∈R,IsCoprime I P)∧(∀P∈T,IsCoprime I P) := by
    constructor
    · intro h
      exact ⟨fun P hP=>h P (Finset.mem_union_left T hP),fun P hP=>h P (Finset.mem_union_right R hP)⟩
    · rintro ⟨hR',hT'⟩ P hP
      exact (Finset.mem_union.mp hP).elim (hR' P) (hT' P)
  simp only [idealCoeff_excludePrimes,hu]
  split_ifs <;> simp_all

theorem row_character_congr (χ ψ : Character) (h : ∀I,idealCoeff χ I=idealCoeff ψ I)
    (S : Finset PrimeIdeal) (pool : ι→Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) :
    row false S χ pool β P W₁ W₂ b X₁ X₂=row false S ψ pool β P W₁ W₂ b X₁ X₂ := by
  unfold row weightedSum naturalCoefficients slotTerm normalizedRow pairCharacter
  simp_rw [h]

open CenteredMomentSourceRectangle

/-- The inherited union of the two ordinary support pools remains the
same union at the exact divided lengths, even if a length is below one. -/
theorem residual_plain_pool (d : Id) (hd : d≠0) (b X Y : ℝ) :
    CenteredMomentFirstSectors.residualPool d hd (plainSupportPool b X Y)=
      plainSupportPool b (X/d.absNorm) (Y/d.absNorm) := by
  have hn : 0<(d.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hd)
  ext I
  have he (A : ℝ) : (d.absNorm:ℝ)*(I.absNorm:ℝ)≤b*A↔
      (I.absNorm:ℝ)≤b*(A/d.absNorm) := by
    rw [show b*(A/(d.absNorm:ℝ))=(b*A)/(d.absNorm:ℝ) by ring,le_div_iff₀ hn]
    rw [mul_comm (I.absNorm:ℝ)]
  simp only [CenteredMomentFirstSectors.mem_residualPool,plainSupportPool,Finset.mem_union,
    mem_idealBall,mul_ne_zero_iff,map_mul,Nat.cast_mul,he]
  constructor
  · rintro (⟨⟨_,hI⟩,hX⟩|⟨⟨_,hI⟩,hY⟩)
    · exact Or.inl ⟨hI,hX⟩
    · exact Or.inr ⟨hI,hY⟩
  · rintro (⟨hI,hX⟩|⟨hI,hY⟩)
    · exact Or.inl ⟨⟨hd,hI⟩,hX⟩
    · exact Or.inr ⟨⟨hd,hI⟩,hY⟩

theorem source_pool_rectangles (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    let A := CenteredMomentFirstSectors.residualPool d.1 hd.1 (plainSupportPool b X₁ Y₁)
    let B := CenteredMomentFirstSectors.residualPool d.2 hd.2 (plainSupportPool b X₂ Y₂)
    rectangle b (X₁/d.1.absNorm) (X₂/d.2.absNorm)⊆A×ˢB ∧
      rectangle b (Y₁/d.1.absNorm) (Y₂/d.2.absNorm)⊆A×ˢB := by
  dsimp only
  rw [residual_plain_pool,residual_plain_pool]
  constructor
  · intro n hn
    have hm := Finset.mem_product.mp hn
    exact Finset.mem_product.mpr ⟨Finset.mem_union_left _ hm.1,Finset.mem_union_left _ hm.2⟩
  · intro n hn
    have hm := Finset.mem_product.mp hn
    exact Finset.mem_product.mpr ⟨Finset.mem_union_right _ hm.1,Finset.mem_union_right _ hm.2⟩

open MixedCommonCoefficient CenteredMomentAddedZeroUniform

/-- Enclose the actual marked pools only after inserting their own
natural zero extension. A missing marked atom makes the entire term zero. -/
theorem centered_pool_completion (χ : Character) (S H : Finset PrimeIdeal)
    (pool : ι→Finset Id) (hpool : ∀i,pool i⊆primeValues S) (A B : Finset Id)
    (β : ι→Id→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) :
    (∑v∈Fintype.piFinset (pools pool A B),tupleWeight (punctureProduct S H) v*
      centeredCoefficient pool β P W₁ W₂ X₁ X₂ Y₁ Y₂ d v*idealCoeff χ (finiteTupleProduct v))=
    ∑v∈Fintype.piFinset (pools (fun _ : ι=>primeValues S) A B),tupleWeight (punctureProduct S H) v*
      centeredCoefficient pool β P W₁ W₂ X₁ X₂ Y₁ Y₂ d v*idealCoeff χ (finiteTupleProduct v) := by
  have hsub : Fintype.piFinset (pools pool A B)⊆
      Fintype.piFinset (pools (fun _ : ι=>primeValues S) A B) := by
    intro v hv
    apply Fintype.mem_piFinset.mpr
    intro j
    cases j with
    | inl i=>exact hpool i (Fintype.mem_piFinset.mp hv (Sum.inl i))
    | inr j=>exact Fintype.mem_piFinset.mp hv (Sum.inr j)
  apply Finset.sum_subset hsub
  intro v hv hn
  by_contra he
  have hc := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp he).1).2
  have hp : (∏i,slotWeight pool β P i (v (Sum.inl i)))≠0 :=
    (mul_ne_zero_iff.mp hc).2
  apply hn
  apply Fintype.mem_piFinset.mpr
  intro j
  cases j with
  | inl i=>
      by_contra hi
      change v (Sum.inl i)∉pool i at hi
      exact (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i))
        (by simp only [slotWeight,ite_eq_right hi])
  | inr j=>exact Fintype.mem_piFinset.mp hv (Sum.inr j)

end
end Candidate.SilPrior.FourthPower.MixedCompletedRows
