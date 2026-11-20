/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.SignedCenterProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Actual finite exceptional polynomials are formed from permitted residual
valuations, with no reciprocal character value or good numerator. The finite
exceptional product costs a subpower of its radical norm. -/
set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

/-- The literal allowed-valuation polynomial at an exceptional prime. Keeping an
arbitrary subset retains fixed seeds and coordinate-specific punctures. -/
def exceptionalLocal (ψ₁ ψ₂ : Character) (P : PrimeIdeal)
    (allowed : Finset (ℕ×ℕ)) (s₁ s₂ : ℂ) : ℂ :=
  ∑ ij ∈ allowed,(eulerVariable ψ₁ P s₁)^ij.1*(eulerVariable ψ₂ P s₂)^ij.2

lemma residualPairs_card : (residualPairs true true).card=6 := by
  decide +kernel

lemma residualPairs_subset (keep₁ keep₂ : Bool) :
    residualPairs keep₁ keep₂ ⊆ residualPairs true true := by
  intro ij hij
  simp only [residualPairs,Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hij ⊢
  exact ⟨hij.1,hij.2.1,by simp,by simp⟩

/-- Every polynomial of permitted cube-free residual valuations has norm at
most six on the 2/5 strip. This includes empty local sources and one-sided holes. -/
theorem exceptionalLocal_norm_le_six (ψ₁ ψ₂ : Character) (P : PrimeIdeal)
    (allowed : Finset (ℕ×ℕ)) (hallowed : allowed ⊆ residualPairs true true)
    (s₁ s₂ : ℂ) (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    ‖exceptionalLocal ψ₁ ψ₂ P allowed s₁ s₂‖ ≤ 6 := by
  have hone : (Ideal.absNorm P.val : ℝ)^(-(2/5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (prime_norm_one_le P) (by norm_num)
  have hx := (eulerVariable_norm_bound ψ₁ P s₁ hs₁).trans hone
  have hy := (eulerVariable_norm_bound ψ₂ P s₂ hs₂).trans hone
  calc
    _ ≤ ∑ ij ∈ allowed,‖(eulerVariable ψ₁ P s₁)^ij.1*(eulerVariable ψ₂ P s₂)^ij.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ij ∈ allowed,(1 : ℝ) := by
      apply Finset.sum_le_sum
      intro ij _hij
      rw [norm_mul,norm_pow,norm_pow]
      have hxpow := pow_le_one₀ (norm_nonneg _) hx (n := ij.1)
      have hypow := pow_le_one₀ (norm_nonneg _) hy (n := ij.2)
      simpa only [one_mul] using mul_le_mul hxpow hypow (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    _ = (allowed.card : ℝ) := by simp
    _ ≤ 6 := by exact_mod_cast (Finset.card_le_card hallowed).trans_eq residualPairs_card

/-- Original modulus zeros remove every positive valuation in that coordinate.
No extra ray character is introduced when a profile prefix is extracted. -/
theorem exceptionalLocal_original_zero_first (ψ₁ ψ₂ : Character) (P : PrimeIdeal)
    (allowed : Finset (ℕ×ℕ)) (s₁ s₂ : ℂ) (hz : idealCoeff ψ₁ P.val=0) :
    exceptionalLocal ψ₁ ψ₂ P allowed s₁ s₂ =
      exceptionalLocal ψ₁ ψ₂ P (allowed.filter fun ij => ij.1=0) s₁ s₂ := by
  unfold exceptionalLocal
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ij hij
  by_cases he : ij.1=0
  · simp [he]
  · simp [he,eulerVariable,hz]

def exceptionalProduct (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (s₁ s₂ : ℂ) : ℂ :=
  ∏ P ∈ bad,exceptionalLocal ψ₁ ψ₂ P (allowed P) s₁ s₂

theorem exceptionalProduct_norm_le (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (hallowed : ∀ P ∈ bad,allowed P ⊆ residualPairs true true)
    (s₁ s₂ : ℂ) (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    ‖exceptionalProduct ψ₁ ψ₂ bad allowed s₁ s₂‖ ≤ (6 : ℝ)^bad.card := by
  unfold exceptionalProduct
  rw [norm_prod]
  calc
    _ ≤ ∏ _P ∈ bad,(6 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun P hP => exceptionalLocal_norm_le_six ψ₁ ψ₂ P (allowed P) (hallowed P hP) s₁ s₂ hs₁ hs₂)
    _ = _ := by simp

/-- A constant per exceptional prime costs only a subpower of the combined
exceptional radical. This is a real norm estimate, not a stored mask margin. -/
theorem six_pow_card_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ bad : Finset PrimeIdeal,
      (6 : ℝ)^bad.card ≤ C*(Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ)^ε := by
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop (6 : ℝ)))
  let K : ℕ := ⌈max 1 B⌉₊
  let small := ConcretePrimeRowBridge.idealsUpTo K
  have hK : max 1 B ≤ (K : ℝ) := Nat.le_ceil _
  refine ⟨(6 : ℝ)^small.card,by positivity,?_⟩
  intro bad
  have hpoint (P : PrimeIdeal) : (6 : ℝ) ≤
      (if P.val ∈ small then 6 else 1)*(Ideal.absNorm P.val : ℝ)^ε := by
    have he : 1 ≤ (Ideal.absNorm P.val : ℝ)^ε := Real.one_le_rpow (prime_norm_one_le P) hε.le
    by_cases hp : P.val ∈ small
    · simp only [ite_eq_left hp]
      nlinarith
    · have hpk : (K : ℝ) < Ideal.absNorm P.val := by
        have hh : ¬Ideal.absNorm P.val ≤ K := by
          intro h
          exact hp (ConcretePrimeRowBridge.mem_idealsUpTo.mpr
            ⟨by exact_mod_cast prime_norm_one_le P,h⟩)
        exact_mod_cast Nat.lt_of_not_ge hh
      simp only [ite_eq_right hp,one_mul]
      exact hB _ ((le_max_right _ _).trans (hK.trans hpk.le))
  have hc : (bad.filter fun P => P.val ∈ small).card ≤ small.card := by
    have hinj : Function.Injective (fun P : PrimeIdeal => P.val) := Subtype.val_injective
    exact (Finset.card_image_of_injective _ hinj).symm ▸
      Finset.card_le_card (fun P hP => by
        obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
        exact (Finset.mem_filter.mp hQ).2)
  calc
    (6 : ℝ)^bad.card = ∏ _P ∈ bad,(6 : ℝ) := by simp
    _ ≤ ∏ P ∈ bad,((if P.val ∈ small then 6 else 1)*(Ideal.absNorm P.val : ℝ)^ε) :=
      Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun P _ => hpoint P)
    _ = (6 : ℝ)^(bad.filter fun P => P.val ∈ small).card *
        (Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ)^ε := by
      rw [Finset.prod_mul_distrib,←Finset.prod_filter]
      simp only [Finset.prod_const,Real.finsetProd_rpow bad _ (fun _ _ => Nat.cast_nonneg _) ε,
        map_prod,Nat.cast_prod]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hc)
      (Real.rpow_nonneg (by positivity) _)

/-- Uniformly over all actual permitted exceptional masks and both heights on
the 2/5 strip. The radical is measured before any hole is forgotten. -/
theorem exceptionalProduct_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
      (allowed : PrimeIdeal → Finset (ℕ×ℕ)),
      (∀ P ∈ bad,allowed P ⊆ residualPairs true true) →
      ∀ s₁ s₂ : ℂ,(2/5 : ℝ) ≤ s₁.re → (2/5 : ℝ) ≤ s₂.re →
      ‖exceptionalProduct ψ₁ ψ₂ bad allowed s₁ s₂‖ ≤
        C*(Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := six_pow_card_subpower ε hε
  exact ⟨C,hC,fun ψ₁ ψ₂ bad allowed hallowed s₁ s₂ hs₁ hs₂ =>
    (exceptionalProduct_norm_le ψ₁ ψ₂ bad allowed hallowed s₁ s₂ hs₁ hs₂).trans (hbound bad)⟩

end
end QRH.Cycle092.SignedCenter
