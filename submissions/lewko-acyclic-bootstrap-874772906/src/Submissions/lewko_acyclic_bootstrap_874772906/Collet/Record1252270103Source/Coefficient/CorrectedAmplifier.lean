/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The exact whole-pool corrected amplifier for the literal normalized Gauss row.
The input coefficient can contain the entire centered rectangle and punctures. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.GaussMask
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

def eligiblePool (P : Finset O) (a : O) : Finset O := P.filter (fun p => ¬p ∣ a)

/-- The multiplier depends on the column and the complete fixed pool, not on
the individual prime or frequency chosen in the outer average. -/
def correctedCoefficient {α : Type*} (P : Finset O) (a : α → O) (c : α → ℂ)
    (i : α) : ℂ := (P.card : ℂ) / ((eligiblePool P (a i)).card : ℂ) * c i

theorem sum_prime_mask (P : Finset O) (a : O) (v : ℂ) :
    (∑ p ∈ P, if p ∣ a then 0 else v) = ((eligiblePool P a).card : ℂ)*v := by
  have he : (∑ p ∈ P, if p ∣ a then 0 else v) = ∑ p ∈ eligiblePool P a, v := by
    simp only [eligiblePool,Finset.sum_filter,ite_not]
  rw [he,Finset.sum_const,nsmul_eq_mul]

/-- Exact undivided CA5. The summand is the original Gauss polynomial, with one
fixed corrected coefficient and every prime of the pool retained. -/
theorem corrected_pool_sum {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (P : Finset O) (hp : ∀ p ∈ P, Prime p)
    (hs : ∀ p ∈ P, Supported (Ideal.span {p}))
    (hg : ∀ p ∈ P, goodLambda ∉ Ideal.span {p})
    (hc : ∀ p ∈ P, ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hsq : ∀ i ∈ S, c i ≠ 0 → ∀ p ∈ P, ¬p^2 ∣ a i)
    (helig : ∀ i ∈ S, c i ≠ 0 → (eligiblePool P (a i)).Nonempty) (h : O) :
    (∑ p ∈ P, gaussPolynomial S a ha (correctedCoefficient P a c) (p^6*h)) =
      (P.card : ℂ)*gaussPolynomial S a ha c h := by
  simp only [gaussPolynomial,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hci : c i = 0
  · simp [correctedCoefficient,hci]
  have hci : c i ≠ 0 := hci
  have hmask : (∑ p ∈ P, correctedCoefficient P a c i * gaussRow (a i) (ha i) (p^6*h)) =
      ∑ p ∈ P, if p ∣ a i then 0 else
        correctedCoefficient P a c i * gaussRow (a i) (ha i) h := by
    apply Finset.sum_congr rfl
    intro p hP
    let : (Ideal.span {p}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (hp p hP).irreducible
    rw [gaussRow_pool_prime_mask (a i) p (ha i) (hp p hP) (hs p hP)
      (hg p hP) (hc p hP) (hsq i hi hci p hP) h]
    split_ifs <;> simp
  rw [hmask,sum_prime_mask]
  have he : ((eligiblePool P (a i)).card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (helig i hi hci).card_pos.ne'
  unfold correctedCoefficient
  field_simp

/-- Exact CA5 in its averaged form. No eligible half-pool and no error family
appears, including at prime-divisible and zero frequencies. -/
theorem corrected_pool_identity {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (P : Finset O) (hP : P.Nonempty) (hp : ∀ p ∈ P, Prime p)
    (hs : ∀ p ∈ P, Supported (Ideal.span {p}))
    (hg : ∀ p ∈ P, goodLambda ∉ Ideal.span {p})
    (hc : ∀ p ∈ P, ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hsq : ∀ i ∈ S, c i ≠ 0 → ∀ p ∈ P, ¬p^2 ∣ a i)
    (helig : ∀ i ∈ S, c i ≠ 0 → (eligiblePool P (a i)).Nonempty) (h : O) :
    gaussPolynomial S a ha c h = (P.card : ℂ)⁻¹ *
      ∑ p ∈ P, gaussPolynomial S a ha (correctedCoefficient P a c) (p^6*h) := by
  rw [corrected_pool_sum S a ha c P hp hs hg hc hsq helig h]
  have hn : (P.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hP.card_pos.ne'
  rw [←mul_assoc,inv_mul_cancel₀ hn,one_mul]

/-- Finite Cauchy for the exact pool average, with the single 1/P payment. -/
theorem norm_average_sq {α : Type*} (P : Finset α) (hP : P.Nonempty) (f : α → ℂ) :
    ‖(P.card : ℂ)⁻¹ * ∑ p ∈ P, f p‖^2 ≤
      (P.card : ℝ)⁻¹ * ∑ p ∈ P, ‖f p‖^2 := by
  have hn : (0 : ℝ) < P.card := Nat.cast_pos.mpr hP.card_pos
  have hsum : ‖∑ p ∈ P, f p‖^2 ≤ (P.card : ℝ)*∑ p ∈ P, ‖f p‖^2 := by
    have ht := norm_sum_le P f
    exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun p _ => norm_nonneg (f p)))).mpr ht).trans
      (sq_sum_le_card_mul_sum_sq (s:=P) (f:=fun p=>‖f p‖))
  rw [norm_mul,norm_inv,Complex.norm_natCast,mul_pow]
  apply (mul_le_mul_of_nonneg_left hsum (sq_nonneg ((P.card : ℝ)⁻¹))).trans_eq
  field_simp

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.corrected_pool_sum
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_pool_identity
#print axioms OAI.SevenEighths.Record1252270103Source.norm_average_sq
