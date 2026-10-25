/- Copyright (c) 2026 Sil. Apache-2.0.
The FULL marked-supplier partition of the actual original column.
Every old tuple restriction, seed, puncture and profile stays in the sum.
 No analytic estimate is assumed.
-/
import Candidate.Feedback.FourthPower.MixedOriginalCoprimality
import Candidate.Feedback.FourthPower.KernelHoleCompletion

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.MixedSupplierPartition
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceCommonMask CenteredMomentSupportedZeroEnergy
open MixedHeightEnergy MixedLiteralAllocation MixedCommonRestriction MixedCommonCoefficient
open MixedCommonAllocation
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- L consists of ALL live (nonsupplier) indices. Its complement consists
of ALL marked suppliers of u. The classification is two-sided. -/
def supplierCharacters (u : Id) (L : Finset α) (ν : α → Id → ℂ) : α → Id → ℂ :=
  KernelHoleCompletion.mixed ν (fun _ P => P ∣ u) L

theorem supplier_character_nonzero (u : Id) (L : Finset α) (ν : α → Id → ℂ)
    (i : α) (P : Id) (h : supplierCharacters u L ν i P ≠ 0) :
    i ∈ L ↔ ¬P ∣ u := by
  by_cases hi : i ∈ L <;> by_cases hP : P ∣ u <;>
    simp [supplierCharacters, KernelHoleCompletion.mixed, KernelHoleCompletion.good,
      KernelHoleCompletion.bad, hi, hP] at h ⊢

/-- The existing product partition is lifted literally to the original
profile. In particular no seed or ordinary rectangle is altered. -/
theorem profile_full_partition (u R : Id) (ν : α → Id → ℂ)
    (Wslot : α → ℝ → ℂ) (P : α → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ seed : Id) (v : Tuple α) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v =
      ∑ L : Finset α, profileCoefficient R (supplierCharacters u L ν) Wslot P
        W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v := by
  have hslot (L : Finset α) (i : α) (I : Id) :
      KernelHoleCompletion.mixed (fun j J => ν j J * Wslot j ((J.absNorm : ℝ)/P j))
        (fun _ J => J ∣ u) L i I =
      supplierCharacters u L ν i I * Wslot i ((I.absNorm : ℝ)/P i) := by
    unfold supplierCharacters KernelHoleCompletion.mixed KernelHoleCompletion.good
      KernelHoleCompletion.bad
    split_ifs <;> simp
  have hp := KernelHoleCompletion.product_partition
    (fun i I => ν i I * Wslot i ((I.absNorm : ℝ)/P i))
    (fun _ I => I ∣ u) (fun i => v (Sum.inl i))
  simp_rw [hslot] at hp
  unfold profileCoefficient
  rw [hp]
  simp only [Finset.sum_mul]

/-- An arbitrary phase or Gauss factor is retained as an exact multiplier
of each tuple. This is an equality before taking any squared norm. -/
theorem weighted_tuple_partition (u H R : Id) (ν : α → Id → ℂ)
    (Wslot : α → ℝ → ℂ) (P : α → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ seed : Id) (v : Tuple α) (F : ℂ) :
    tupleWeight H v * profileCoefficient R ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ seed v * F =
      ∑ L : Finset α, tupleWeight H v *
        profileCoefficient R (supplierCharacters u L ν) Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ B₁ B₂ seed v * F := by
  rw [profile_full_partition u R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v]
  simp only [Finset.mul_sum, Finset.sum_mul]

/-- Exact identity for the actual originalColumn, with no coefficient
separation hypothesis and no claim that a partial supplier list suffices. -/
theorem originalColumn_full_partition (u : Id) (S H : Finset PrimeIdeal)
    (pool : α → Finset Id) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id)
    (ν : α → Id → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (I : Id) :
    originalColumn S H pool d hd R seed ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ I =
      ∑ L : Finset α, originalColumn S H pool d hd R seed (supplierCharacters u L ν)
        Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ I := by
  unfold originalColumn finiteColumnCoefficient
  simp_rw [profile_full_partition u R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 seed]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Column phases, including an unsplit reciprocity phase, remain intact.
F is not required to be independent of I; it is the same function in
every partition summand. -/
theorem originalColumn_phase_partition (u : Id) (S H : Finset PrimeIdeal)
    (pool : α → Finset Id) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id)
    (ν : α → Id → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (Q : Finset Id) (F : Id → ℂ) :
    (∑ I ∈ Q, originalColumn S H pool d hd R seed ν Wslot P
      W₁ W₂ b X₁ X₂ Y₁ Y₂ I * F I) =
      ∑ L : Finset α, ∑ I ∈ Q,
        originalColumn S H pool d hd R seed (supplierCharacters u L ν)
          Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ I * F I := by
  simp_rw [originalColumn_full_partition u S H pool d hd R seed ν Wslot P
    W₁ W₂ b X₁ X₂ Y₁ Y₂]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Every nonzero tuple in one partition branch has exactly the declared
supplier set. Cancellations in a column do not weaken this statement. -/
theorem nonzero_profile_supplier_set (u R : Id) (L : Finset α) (ν : α → Id → ℂ)
    (Wslot : α → ℝ → ℂ) (P : α → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ seed : Id) (v : Tuple α)
    (hne : profileCoefficient R (supplierCharacters u L ν) Wslot P
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v ≠ 0) :
    ∀ i, i ∈ L ↔ ¬v (Sum.inl i) ∣ u := by
  have hp : (∏ j, supplierCharacters u L ν j (v (Sum.inl j)) *
      Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ)/P j)) ≠ 0 := by
    intro hz
    exact hne (by simp only [profileCoefficient, hz, zero_mul])
  intro i
  exact supplier_character_nonzero u L ν i (v (Sum.inl i))
    (mul_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i))).1

/-- This is the needed selected-block coprimality, proved from the
literal branch coefficient and actual prime slots. It is not an added
structural assumption. No squarefreeness of u is needed for this step. -/
theorem selected_product_coprime (u R : Id) (L J : Finset α) (hJL : J ⊆ L)
    (ν : α → Id → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ seed : Id) (v : Tuple α)
    (hp : ∀ i, Prime (v (Sum.inl i)))
    (hne : profileCoefficient R (supplierCharacters u L ν) Wslot P
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v ≠ 0) :
    IsCoprime u (∏ i ∈ J, v (Sum.inl i)) := by
  have hslots := nonzero_profile_supplier_set u R L ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ seed v hne
  apply IsCoprime.prod_right
  intro i hi
  exact ((prime_coprime ⟨v (Sum.inl i), hp i⟩ u).mpr
    ((hslots i).mp (hJL hi))).symm

/-- A nonzero actual original-column branch supplies a literal tuple,
all restrictions, the complete supplier classification, and the
selected-product coprimality required by the Gauss adapter. -/
theorem originalColumn_supplier_witness (u : Id) (L J : Finset α) (hJL : J ⊆ L)
    (S H : Finset PrimeIdeal) (pool : α → Finset Id)
    (hp : ∀ i, ∀ I ∈ pool i, Prime I)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id)
    (ν : α → Id → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (I : Id)
    (hne : originalColumn S H pool d hd R seed (supplierCharacters u L ν)
      Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ I ≠ 0) :
    ∃ v ∈ Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂),
      finiteTupleProduct v = I ∧ tupleRestriction (punctureProduct S H) v ∧
      profileCoefficient R (supplierCharacters u L ν) Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ d.1 d.2 seed v ≠ 0 ∧
      (∀ i, i ∈ L ↔ ¬v (Sum.inl i) ∣ u) ∧
      IsCoprime u (∏ i ∈ J, v (Sum.inl i)) := by
  obtain ⟨v,hv,hweight,hvI⟩ := finiteColumnCoefficient_witness
    (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
    (fun v => tupleWeight (punctureProduct S H) v *
      profileCoefficient R (supplierCharacters u L ν) Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ d.1 d.2 seed v) I hne
  have hr : tupleRestriction (punctureProduct S H) v := by
    by_contra hnot
    exact hweight (by simp [tupleWeight, hnot])
  have hprof := (mul_ne_zero_iff.mp hweight).2
  refine ⟨v,hv,hvI,hr,hprof,
    nonzero_profile_supplier_set u R L ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ d.1 d.2 seed v hprof, ?_⟩
  apply selected_product_coprime u R L J hJL ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ d.1 d.2 seed v _ hprof
  intro i
  exact hp i _ (Fintype.mem_piFinset.mp hv (Sum.inl i))

end
end Candidate.Feedback.FourthPower.MixedSupplierPartition
