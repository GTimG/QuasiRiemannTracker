/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.SignedCenterMass

/-! Restore the actual original ordinary characters as the base L-factors by
multiplying the exceptional residual polynomials by finite Euler deletion
numerators. This avoids inventing a new row identity after deleting primes.
-/
set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

def deletionExponent₁ (j : Fin 4) : ℕ := ![0,0,1,1] j

def deletionExponent₂ (j : Fin 4) : ℕ := ![0,1,0,1] j

def deletionTerm (x y : ℂ) (j : Fin 4) : ℂ :=
  (-x)^deletionExponent₁ j*(-y)^deletionExponent₂ j

lemma deletionTerm_sum (x y : ℂ) : ∑ j : Fin 4,deletionTerm x y j=(1-x)*(1-y) := by
  norm_num [deletionTerm,deletionExponent₁,deletionExponent₂,Fin.sum_univ_succ]
  ring

abbrev DeletionIndex (bad : Finset PrimeIdeal) := bad → Fin 4

def deletionSeriesTerm (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal) (s₁ s₂ : ℂ)
    (k : DeletionIndex bad) : ℂ :=
  ∏ P : bad,deletionTerm (eulerVariable χ₁ P.val s₁) (eulerVariable χ₂ P.val s₂) (k P)

def deletionCoefficient (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal) (k : DeletionIndex bad) : ℂ :=
  ∏ P : bad,deletionTerm (idealCoeff χ₁ P.val.val) (idealCoeff χ₂ P.val.val) (k P)

def deletionIdeal₁ (bad : Finset PrimeIdeal) (k : DeletionIndex bad) : Ideal O :=
  ∏ P : bad,P.val.val^deletionExponent₁ (k P)

def deletionIdeal₂ (bad : Finset PrimeIdeal) (k : DeletionIndex bad) : Ideal O :=
  ∏ P : bad,P.val.val^deletionExponent₂ (k P)

lemma deletionIdeal₁_ne_zero (bad : Finset PrimeIdeal) (k : DeletionIndex bad) : deletionIdeal₁ bad k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => pow_ne_zero _ P.val.property.ne_zero)

lemma deletionIdeal₂_ne_zero (bad : Finset PrimeIdeal) (k : DeletionIndex bad) : deletionIdeal₂ bad k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => pow_ne_zero _ P.val.property.ne_zero)

lemma deletionSeriesTerm_coefficient (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal)
    (s₁ s₂ : ℂ) (k : DeletionIndex bad) :
    deletionSeriesTerm χ₁ χ₂ bad s₁ s₂ k=deletionCoefficient χ₁ χ₂ bad k*
      IdealEuler.normWeight s₁ (deletionIdeal₁ bad k)*IdealEuler.normWeight s₂ (deletionIdeal₂ bad k) := by
  simp only [deletionSeriesTerm,deletionTerm,eulerVariable_eq_normWeight,neg_mul,mul_pow,
    deletionCoefficient,deletionIdeal₁,deletionIdeal₂,map_prod,map_pow]
  rw [←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  ring

lemma deletionSeries_expansion (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal) (s₁ s₂ : ℂ) :
    (∏ P ∈ bad,(1-eulerVariable χ₁ P s₁)*(1-eulerVariable χ₂ P s₂))=
      ∑ k : DeletionIndex bad,deletionSeriesTerm χ₁ χ₂ bad s₁ s₂ k := by
  simp_rw [←deletionTerm_sum]
  rw [←Finset.prod_coe_sort bad,Fintype.prod_sum]
  rfl

lemma deletionSeries_mass_le (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal) (s₁ s₂ : ℂ)
    (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    (∑ k : DeletionIndex bad,‖deletionSeriesTerm χ₁ χ₂ bad s₁ s₂ k‖) ≤ (4 : ℝ)^bad.card := by
  have hx (χ : Character) (P : PrimeIdeal) (s : ℂ) (hs : (2/5 : ℝ) ≤ s.re) : ‖eulerVariable χ P s‖ ≤ 1 :=
    (eulerVariable_norm_bound χ P s hs).trans
      (Real.rpow_le_one_of_one_le_of_nonpos (prime_norm_one_le P) (by norm_num))
  have hterm (k : DeletionIndex bad) : ‖deletionSeriesTerm χ₁ χ₂ bad s₁ s₂ k‖ ≤ 1 := by
    rw [deletionSeriesTerm,norm_prod]
    apply Finset.prod_le_one₀
    · intro P _
      exact norm_nonneg _
    · intro P _
      rw [deletionTerm,norm_mul,norm_pow,norm_pow,norm_neg,norm_neg]
      have h₁ := pow_le_one₀ (norm_nonneg _) (hx χ₁ P.val s₁ hs₁) (n := deletionExponent₁ (k P))
      have h₂ := pow_le_one₀ (norm_nonneg _) (hx χ₂ P.val s₂ hs₂) (n := deletionExponent₂ (k P))
      simpa only [one_mul] using mul_le_mul h₁ h₂ (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
  calc
    _ ≤ ∑ _k : DeletionIndex bad,(1 : ℝ) := Finset.sum_le_sum (fun k _ => hterm k)
    _ = _ := by simp [DeletionIndex,Fintype.card_fun]

abbrev CorrectedIndex (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) :=
  DeletionIndex bad × FullIndex bad allowed

def correctedCoefficient (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (k : CorrectedIndex bad allowed) : ℂ :=
  deletionCoefficient χ₁ χ₂ bad k.1*fullCoefficient ψ₁ ψ₂ bad allowed k.2

def correctedIdeal₁ (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (k : CorrectedIndex bad allowed) : Ideal O := deletionIdeal₁ bad k.1*fullIdeal₁ bad allowed k.2

def correctedIdeal₂ (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (k : CorrectedIndex bad allowed) : Ideal O := deletionIdeal₂ bad k.1*fullIdeal₂ bad allowed k.2

lemma correctedIdeal₁_ne_zero (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (k : CorrectedIndex bad allowed) : correctedIdeal₁ bad allowed k ≠ 0 :=
  mul_ne_zero (deletionIdeal₁_ne_zero bad k.1) (fullIdeal₁_ne_zero bad allowed k.2)

lemma correctedIdeal₂_ne_zero (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (k : CorrectedIndex bad allowed) : correctedIdeal₂ bad allowed k ≠ 0 :=
  mul_ne_zero (deletionIdeal₂_ne_zero bad k.1) (fullIdeal₂_ne_zero bad allowed k.2)

def correctedSeriesTerm (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (s₁ s₂ : ℂ) (k : CorrectedIndex bad allowed) : ℂ :=
  deletionSeriesTerm χ₁ χ₂ bad s₁ s₂ k.1*fullSeriesTerm ψ₁ ψ₂ bad allowed s₁ s₂ k.2

lemma correctedSeriesTerm_coefficient (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (s₁ s₂ : ℂ) (k : CorrectedIndex bad allowed) :
    correctedSeriesTerm χ₁ χ₂ ψ₁ ψ₂ bad allowed s₁ s₂ k=
      correctedCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed k*
      IdealEuler.normWeight s₁ (correctedIdeal₁ bad allowed k)*
      IdealEuler.normWeight s₂ (correctedIdeal₂ bad allowed k) := by
  rw [correctedSeriesTerm,deletionSeriesTerm_coefficient,fullSeriesTerm_coefficient]
  simp only [correctedCoefficient,correctedIdeal₁,correctedIdeal₂,map_mul]
  ring

lemma correctedSeries_summable_norm (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (s₁ s₂ : ℂ)
    (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    Summable (fun k : CorrectedIndex bad allowed => ‖correctedSeriesTerm χ₁ χ₂ ψ₁ ψ₂ bad allowed s₁ s₂ k‖) := by
  have hd : Summable (fun k : DeletionIndex bad => ‖deletionSeriesTerm χ₁ χ₂ bad s₁ s₂ k‖) := (hasSum_fintype _).summable
  have hf := fullSeries_summable_norm ψ₁ ψ₂ bad allowed s₁ s₂ hs₁ hs₂
  simpa only [correctedSeriesTerm,norm_mul,norm_norm] using hd.mul_norm hf

theorem correctedCoefficient_weighted_summable (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) :
    Summable (fun k : CorrectedIndex bad allowed => ‖correctedCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed k‖*
      ((Ideal.absNorm (correctedIdeal₁ bad allowed k) : ℝ)*
        (Ideal.absNorm (correctedIdeal₂ bad allowed k) : ℝ))^(-(2/5 : ℝ))) := by
  apply (correctedSeries_summable_norm χ₁ χ₂ ψ₁ ψ₂ bad allowed (2/5 : ℂ) (2/5 : ℂ)
    (by norm_num) (by norm_num)).congr
  intro k
  rw [correctedSeriesTerm_coefficient,norm_mul,norm_mul,
    normWeight_critical _ (correctedIdeal₁_ne_zero bad allowed k),
    normWeight_critical _ (correctedIdeal₂_ne_zero bad allowed k),
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

end
end QRH.Cycle092.SignedCenter
