/- Copyright (c) 2026 Sil. Apache-2.0.
Exact GCD and Mobius descent adapted from OpenAI baseline CubicSieve.Gcd
and CubicSieve.Mobius. The rows are sextic, and no squarefree restriction
is imposed on the columns or their common divisor. Generic quotient and
finite-sum reindexing functions are imported unchanged from the baseline. -/
import Candidate.FourthPower.SievePairPoisson
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CubicSieve.Mobius

set_option autoImplicit false
namespace Candidate.FourthPower.SieveGcd
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open CanonicalRowCompletion CanonicalQuadraticSieve
open CubicSieve (dividedRows sum_divisible_rows ideal_dvd_span_iff_generator)
open SexticSieve
local notation "O" => ActualEisensteinCubic.O

def row (I : Ideal O) (z : O) : ℂ := idealRowHom z I

theorem row_mul_column (I J : Ideal O) (z : O) : row (I*J) z = row I z * row J z :=
  map_mul (idealRowHom z) I J

theorem row_mul_argument (I : Ideal O) (x y : O) : row I (x*y) = row I x * row I y :=
  idealRowHom_argument_mul x y I

theorem common_mask (D : Ideal O) (hD : Supported D) (z : O) :
    star (row D z) * row D z = if IsCoprime D (Ideal.span {z}) then 1 else 0 := by
  have hp : row D z ^ 6 = if IsCoprime D (Ideal.span {z}) then 1 else 0 := by
    dsimp only [row]
    rw [← idealRowHom_argument_pow z 6 D hD, idealRowHom_sixth_mask z D hD]
  split_ifs at hp ⊢ with hc
  · have hn := congrArg norm hp
    simp only [norm_pow, norm_one] at hn
    have hn1 : ‖row D z‖ = 1 :=
      (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (6 : ℕ) ≠ 0)).mp
        (hn.trans (one_pow 6).symm)
    rw [mul_comm, ← starRingEnd_apply, Complex.mul_conj', hn1]
    norm_num
  · have hz : row D z = 0 := by simpa only [pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)] using hp
    simp only [hz, star_zero, zero_mul]

theorem common_mobius (D : Ideal O) (hD : Supported D) (z : O) :
    star (row D z) * row D z =
      ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        if E ∣ Ideal.span {z} then (UniqueFactorizationMonoid.moebius E : ℂ) else 0 := by
  rw [common_mask D hD z]
  exact InverseMoment.ideal_coprime_mobius D _ hD.1

lemma row_divisor_factor (D I : Ideal O) (hDI : D ∣ I) (z : O) :
    row I z = row D z * row (idealQuotient D I) z := by
  conv_lhs => rw [← CanonicalQuadraticSieve.idealQuotient_mul hDI]
  exact row_mul_column _ _ _

def gcdTerm {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) (j k : n) : ℂ :=
  if gcd (cols j) (cols k) = D then
    star (row (cols j) z * a j) * (row (cols k) z * a k) else 0

theorem gcdTerm_eq_quotient {n : Type*}
    (D : Ideal O) (hD : D ≠ 0) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) (j k : n) :
    gcdTerm D cols a z j k =
      (star (row D z) * row D z) *
      (if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (row (totalQuotient D (cols j)) z * (if D ∣ cols j then a j else 0)) *
          (row (totalQuotient D (cols k)) z * (if D ∣ cols k then a k else 0)) else 0) := by
  by_cases hj : D ∣ cols j
  · by_cases hk : D ∣ cols k
    · simp only [gcdTerm, totalQuotient, ite_eq_left hj, ite_eq_left hk]
      rw [← CanonicalQuadraticSieve.gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD hj hk]
      by_cases hg : gcd (cols j) (cols k) = D
      · rw [ite_eq_left hg, ite_eq_left hg, row_divisor_factor D _ hj,
          row_divisor_factor D _ hk]
        simp only [star_mul]
        ring
      · simp only [ite_eq_right hg, mul_zero]
    · have hg : gcd (cols j) (cols k) ≠ D := by
        intro he
        exact hk (he ▸ gcd_dvd_right (cols j) (cols k))
      simp only [gcdTerm, ite_eq_right hg]
      simp [hk]
  · have hg : gcd (cols j) (cols k) ≠ D := by
      intro he
      exact hj (he ▸ gcd_dvd_left (cols j) (cols k))
    simp only [gcdTerm, ite_eq_right hg]
    simp [hj]

theorem weighted_energy_eq_gcd_blocks {n : Type*} [Fintype n]
    (R : Finset O) (w : O → ℂ) (cols : n → Ideal O) (a : n → ℂ) :
    (∑ z ∈ R, w z * (‖∑ j, row (cols j) z * a j‖ ^ 2 : ℝ)) =
      ∑ D ∈ gcdPool cols, ∑ z ∈ R, w z * ∑ j, ∑ k, gcdTerm D cols a z j k := by
  have hp (z : O) (j k : n) :
      (∑ D ∈ gcdPool cols, gcdTerm D cols a z j k) =
      star (row (cols j) z * a j) * (row (cols k) z * a k) := by
    rw [Finset.sum_eq_single (gcd (cols j) (cols k))]
    · simp only [gcdTerm, ite_true]
    · intro D hD hne
      exact ite_eq_right (Ne.symm hne)
    · exact fun h => (h (CanonicalQuadraticSieve.mem_gcdPool cols j k)).elim
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => arg 2; ext j; rw [Finset.sum_comm]
  simp_rw [hp]
  simpa only [Complex.ofReal_pow] using CoprimeSieveOperator.square_norm_sum
    (fun j => row (cols j) z * a j)

def descendedCoefficient {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (d : O) (j : n) : ℂ :=
  row (totalQuotient D (cols j)) d * (if D ∣ cols j then a j else 0)

def residualGram {n : Type*} [Fintype n] (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
    star (row (totalQuotient D (cols j)) z * a j) *
      (row (totalQuotient D (cols k)) z * a k) else 0

lemma residualGram_rescale {n : Type*} [Fintype n] (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (d w : O) :
    residualGram D cols (fun j => if D ∣ cols j then a j else 0) (d * w) =
      residualGram D cols (descendedCoefficient D cols a d) w := by
  unfold residualGram
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs
  · rw [row_mul_argument,
      row_mul_argument]
    simp only [descendedCoefficient, star_mul]
    ring
  · rfl


lemma sum_dividedRows_residualGram_rescale {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) 
    (a : n → ℂ) (R : Finset O) (w : O → ℂ) (d : O) :
    (∑ z ∈ dividedRows R d,
      w (d * z) * residualGram D cols (fun j => if D ∣ cols j then a j else 0) (d * z)) =
      ∑ z ∈ dividedRows R d,
        w (d * z) * residualGram D cols (descendedCoefficient D cols a d) z := by
  apply Finset.sum_congr rfl
  intro z _
  rw [residualGram_rescale D cols a]

theorem gcd_mobius_descent {n : Type*} [Fintype n]
    (D : Ideal O) (hD : Supported D)
    (cols : n → Ideal O) 
    (a : n → ℂ) (R : Finset O) (w : O → ℂ) :
    (∑ z ∈ R, w z * ∑ j, ∑ k, gcdTerm D cols a z j k) =
      ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          ∑ z ∈ dividedRows R (idealGenerator E),
            w (idealGenerator E * z) *
              residualGram D cols (descendedCoefficient D cols a (idealGenerator E)) z := by
  let b : n → ℂ := fun j => if D ∣ cols j then a j else 0
  have ht (z : O) : (∑ j, ∑ k, gcdTerm D cols a z j k) =
      (star (row D z) * row D z) * residualGram D cols b z := by
    simp only [gcdTerm_eq_quotient D hD.1,
      residualGram, b, Finset.mul_sum]
  calc
    _ = ∑ z ∈ R, ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          (if idealGenerator E ∣ z then w z * residualGram D cols b z else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [ht, common_mobius D hD, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E hE
      rw [ideal_dvd_span_iff_generator]
      split_ifs <;> ring
    _ = ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          ∑ z ∈ R, if idealGenerator E ∣ z then w z * residualGram D cols b z else 0 := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [sum_divisible_rows]
      exact congrArg ((UniqueFactorizationMonoid.moebius E : ℂ) * ·)
        (sum_dividedRows_residualGram_rescale D cols a R w (idealGenerator E))

open IdealMobiusDivisorSum

theorem descendedCoefficient_norm_sq {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (d : O) (j : n) :
    ‖descendedCoefficient D cols a d j‖^2 ≤ if D ∣ cols j then ‖a j‖^2 else 0 := by
  by_cases hj : D ∣ cols j
  · simp only [descendedCoefficient,ite_eq_left hj,norm_mul]
    apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _ 2
    exact mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)
  · simp only [descendedCoefficient,ite_eq_right hj,mul_zero,norm_zero,zero_pow (by decide : (2:ℕ)≠0),le_refl]

theorem divisorCard_mono (D I : Ideal O) (hI : I ≠ 0) (hDI : D ∣ I) :
    (idealDivisors D).card ≤ (idealDivisors I).card := by
  have hD : D ≠ 0 := by
    intro hz
    rw [hz,zero_dvd_iff] at hDI
    exact hI hDI
  apply Finset.card_le_card
  intro E hE
  exact (mem_idealDivisors hI).mpr (((mem_idealDivisors hD).mp hE).trans hDI)

theorem nested_divisor_count (S : Finset (Ideal O)) (I : Ideal O) (hI : I ≠ 0) :
    (∑ D ∈ S, if D ∣ I then ((idealDivisors D).card : ℝ) else 0) ≤
      ((idealDivisors I).card : ℝ)^2 := by
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ D ∈ idealDivisors I, ((idealDivisors D).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun D hD => (mem_idealDivisors hI).mpr (Finset.mem_filter.mp hD).2)
        (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ ∑ _D ∈ idealDivisors I, ((idealDivisors I).card : ℝ) :=
      Finset.sum_le_sum (fun D hD => Nat.cast_le.mpr
        (divisorCard_mono D I hI ((mem_idealDivisors hI).mp hD)))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,pow_two]

/-- GCD sorting and the subsequent Mobius expansion cost only an arbitrary
small power, even when every original column has repeated prime factors. -/
theorem descended_mass (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : Type*} [Fintype n] (S : Finset (Ideal O))
      (cols : n → Ideal O), (∀ j, cols j ≠ 0) →
      ∀ (B : ℝ), 1 ≤ B → (∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ B) →
      ∀ a : n → ℂ,
      (∑ D ∈ S, ∑ E ∈ idealDivisors D, ∑ j,
        ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) ≤
          C*B^ε*∑ j, ‖a j‖^2 := by
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/2) (by positivity)
  refine ⟨C^2,pow_pos hC 2,?_⟩
  intro n _ S cols hc B hB hN a
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hj (j : n) : ((idealDivisors (cols j)).card : ℝ)^2 ≤ C^2*B^ε := by
    have hb : ((idealDivisors (cols j)).card : ℝ) ≤ C*B^(ε/2) :=
      (hdiv (cols j) (hc j)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hN j) (by positivity)) hC.le)
    have he : (C*B^(ε/2))^2 = C^2*B^ε := by
      rw [mul_pow,pow_two (B^(ε/2)),← Real.rpow_add hB0]
      congr 2
      ring
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hb 2).trans_eq he
  calc
    _ ≤ ∑ D ∈ S, ∑ E ∈ idealDivisors D, ∑ j, if D ∣ cols j then ‖a j‖^2 else 0 :=
      Finset.sum_le_sum (fun D _ => Finset.sum_le_sum (fun E _ =>
        Finset.sum_le_sum (fun j _ => descendedCoefficient_norm_sq D cols a _ j)))
    _ = ∑ j, (∑ D ∈ S, if D ∣ cols j then ((idealDivisors D).card : ℝ) else 0)*‖a j‖^2 := by
      conv_lhs => arg 2; ext D; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro D _
      by_cases h : D ∣ cols j <;> simp [h]
    _ ≤ ∑ j, (C^2*B^ε)*‖a j‖^2 := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right ((nested_divisor_count S (cols j) (hc j)).trans (hj j)) (sq_nonneg _))
    _ = _ := (Finset.mul_sum _ _ _).symm

end
end Candidate.FourthPower.SieveGcd
