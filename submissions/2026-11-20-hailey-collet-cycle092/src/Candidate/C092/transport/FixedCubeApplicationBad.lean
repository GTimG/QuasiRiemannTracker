/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.FixedCubeApplicationCharacter

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

/-- All literal prime labels (supplying primes, coordinate punctures, fixed
bad primes and any seed primes) enter through their actual product. -/
def fixedCubeBadIdeal (D₁ D₂ : FixedCubeDatum) (labels : Finset PrimeIdeal) : Ideal O :=
  D₁.row.χ.modulus*D₂.row.χ.modulus*(∏ P ∈ labels,P.val)

lemma fixedCubeBadIdeal_ne_zero (D₁ D₂ : FixedCubeDatum) (labels : Finset PrimeIdeal) :
    fixedCubeBadIdeal D₁ D₂ labels ≠ 0 :=
  mul_ne_zero (mul_ne_zero D₁.row.χ.modulus_ne_bot D₂.row.χ.modulus_ne_bot)
    (Finset.prod_ne_zero_iff.mpr (fun P _ => P.property.ne_zero))

/-- Canonical finite bad set derived from actual presented moduli and labels;
coverage of their holes is proved below rather than supplied as a premise. -/
def fixedCubeBad (D₁ D₂ : FixedCubeDatum) (labels : Finset PrimeIdeal) : Finset PrimeIdeal :=
  (ProbePhysical.primeValuations (fixedCubeBadIdeal D₁ D₂ labels)).support

lemma prime_coprime_outside_support (M : Ideal O) (hM : M ≠ 0) (P : PrimeIdeal)
    (hP : P ∉ (ProbePhysical.primeValuations M).support) : IsCoprime P.val M := by
  rw [←ProbePhysical.idealFromValuations_primeValuations M hM]
  exact ProbePhysical.prime_coprime_idealFromValuations P _ (Finsupp.notMem_support_iff.mp hP)

lemma prime_dvd_mem_support (M : Ideal O) (hM : M ≠ 0) (P : PrimeIdeal) (hd : P.val ∣ M) :
    P ∈ (ProbePhysical.primeValuations M).support := by
  by_contra hn
  have hc := prime_coprime_outside_support M hM P hn
  exact P.property.not_isUnit (hc.isUnit_of_dvd hd)

lemma fixedCubeBad_contains_labels (D₁ D₂ : FixedCubeDatum) (labels : Finset PrimeIdeal) :
    labels ⊆ fixedCubeBad D₁ D₂ labels := by
  intro P hP
  apply prime_dvd_mem_support _ (fixedCubeBadIdeal_ne_zero D₁ D₂ labels) P
  exact (Finset.dvd_prod_of_mem (fun P : PrimeIdeal => P.val) hP).trans (dvd_mul_left _ _)

/-- Both original presented-modulus masks are covered by the constructed bad
set; no extra prime-agreement or character-nonvanishing assumption is used. -/
theorem fixedCubeBad_good (D₁ D₂ : FixedCubeDatum) (labels : Finset PrimeIdeal)
    (P : PrimeIdeal) (hP : P ∉ fixedCubeBad D₁ D₂ labels) :
    IsCoprime P.val D₁.row.χ.modulus ∧ IsCoprime P.val D₂.row.χ.modulus := by
  have hc := prime_coprime_outside_support _ (fixedCubeBadIdeal_ne_zero D₁ D₂ labels) P hP
  refine ⟨hc.of_isCoprime_of_dvd_right ?_,hc.of_isCoprime_of_dvd_right ?_⟩
  · exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  · exact (dvd_mul_left _ _).trans (dvd_mul_right _ _)

lemma primeSupport_product_dvd (M : Ideal O) (hM : M ≠ 0) :
    (∏ P ∈ (ProbePhysical.primeValuations M).support,P.val) ∣ M := by
  apply Finset.prod_dvd_of_coprime
  · intro P _ Q _ hPQ
    exact ProbePhysical.primeIdeal_coprime P Q hPQ
  · intro P hP
    apply (ideal_dvd_iff_valuations_le P.val M P.property.ne_zero hM).mpr
    rw [ProbePhysical.primeValuations_prime]
    intro Q
    by_cases hQ : Q=P
    · subst Q
      simpa only [Finsupp.single_apply,ite_true] using
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hP)
    · simp only [Finsupp.single_apply,ite_eq_right (Ne.symm hQ),Nat.zero_le]

/-- The actual exceptional radical is bounded by the original two presented
moduli times the literal label product, including collisions among these sets. -/
theorem fixedCubeBad_radical_norm (D₁ D₂ : FixedCubeDatum) (labels : Finset PrimeIdeal) :
    (Ideal.absNorm (∏ P ∈ fixedCubeBad D₁ D₂ labels,P.val) : ℝ) ≤
      (Ideal.absNorm D₁.row.χ.modulus : ℝ)*(Ideal.absNorm D₂.row.χ.modulus : ℝ)*
        (Ideal.absNorm (∏ P ∈ labels,P.val) : ℝ) := by
  have hn := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (fixedCubeBadIdeal_ne_zero D₁ D₂ labels)))
    (map_dvd Ideal.absNorm (primeSupport_product_dvd _ (fixedCubeBadIdeal_ne_zero D₁ D₂ labels)))
  change (Ideal.absNorm (∏ P ∈ fixedCubeBad D₁ D₂ labels,P.val) : ℕ) ≤ _ at hn
  have hr : (Ideal.absNorm (∏ P ∈ fixedCubeBad D₁ D₂ labels,P.val) : ℝ) ≤
      (Ideal.absNorm (fixedCubeBadIdeal D₁ D₂ labels) : ℝ) := by exact_mod_cast hn
  simpa only [fixedCubeBadIdeal,map_mul,Nat.cast_mul] using hr

/-- Discharges H8's separate exceptional-radical norm cap from the original
row-conductor caps and the actual prime-label product cap. -/
theorem fixedCubeBad_polynomial_cap (D₁ D₂ : FixedCubeDatum) (labels : Finset PrimeIdeal)
    (U B₁ B₂ B₃ : ℝ) (hU : 0 < U)
    (h₁ : (HeckeRowClosure.rowConductorBound D₁.η D₁.m 1 (D₁.A*D₁.z) : ℝ) ≤ U^B₁)
    (h₂ : (HeckeRowClosure.rowConductorBound D₂.η D₂.m 1 (D₂.A*D₂.z) : ℝ) ≤ U^B₂)
    (h₃ : (Ideal.absNorm (∏ P ∈ labels,P.val) : ℝ) ≤ U^B₃) :
    (Ideal.absNorm (∏ P ∈ fixedCubeBad D₁ D₂ labels,P.val) : ℝ) ≤ U^(B₁+B₂+B₃) := by
  have hχ₁ : (Ideal.absNorm D₁.row.χ.modulus : ℝ) ≤ U^B₁ := by
    apply le_trans _ h₁
    exact_mod_cast D₁.row_spec.2.1
  have hχ₂ : (Ideal.absNorm D₂.row.χ.modulus : ℝ) ≤ U^B₂ := by
    apply le_trans _ h₂
    exact_mod_cast D₂.row_spec.2.1
  apply (fixedCubeBad_radical_norm D₁ D₂ labels).trans
  calc
    _ ≤ (U^B₁*U^B₂)*U^B₃ :=
      mul_le_mul (mul_le_mul hχ₁ hχ₂ (Nat.cast_nonneg _) (Real.rpow_nonneg hU.le _)) h₃
        (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg hU.le _) (Real.rpow_nonneg hU.le _))
    _ = _ := by rw [Real.rpow_add hU,Real.rpow_add hU]

#print axioms fixedCubeBad_good
#print axioms fixedCubeBad_radical_norm
#print axioms fixedCubeBad_polynomial_cap
end
end QRH.Cycle092.SignedCenter
