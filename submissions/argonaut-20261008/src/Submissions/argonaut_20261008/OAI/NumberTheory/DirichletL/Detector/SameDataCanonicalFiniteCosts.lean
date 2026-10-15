import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.SameDataCanonicalBudgets
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralFiniteError

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.PerturbedCanonicalLocalPrep
open HeckeFamily ProbePhysical ProbeMellinBoundary
open HeckeInverseAmplification hiding PrimeIdeal
open SevenEighths.Parameters SevenEighths.PerturbedCentral
open SevenEighths.ProbeHighRowFamily
local notation "O" => HeckeFamily.O

theorem same_D_canonical_prime_product {Delta : ℝ} (D : HighDataPerturbed Delta)
    (P : Fin D.N → PrimeIdeal) (Z b : ℝ) (hZ : 0 < Z)
    (hP : ∀j, ((P j).val.absNorm : ℝ) ≤ b * Z ^ D.ell j) :
    (∏j, ((P j).val.absNorm : ℝ)) ≤ b ^ D.N * Z ^ totalE := by
  have hsum : ∑j, D.ell j = totalE := by
    simpa only [totalE, rho0, perturbedTotalE, perturbedRho] using D.slots_sum
  calc
    _ ≤ ∏j, b * Z ^ D.ell j :=
      Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => hP j)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← Real.rpow_sum_of_pos hZ, hsum]

theorem same_D_canonical_prime_tuple_count {Delta : ℝ} (D : HighDataPerturbed Delta)
    (T : Fin D.N → Finset PrimeIdeal) (Z b : ℝ) (hZ : 0 < Z) (hb : 0 ≤ b)
    (hT : ∀j P, P ∈ T j → (P.val.absNorm : ℝ) ≤ b * Z ^ D.ell j) :
    (Fintype.card (∀j, T j) : ℝ) ≤ (128 * b) ^ D.N * Z ^ totalE := by
  have hsum : ∑j, D.ell j = totalE := by
    simpa only [totalE, rho0, perturbedTotalE, perturbedRho] using D.slots_sum
  have hc (j : Fin D.N) : ((T j).card : ℝ) ≤ 128 * b * Z ^ D.ell j := by
    have hh := ProbeSelectedPrimeSums.finite_ideal_count ((T j).image Subtype.val)
      (b * Z ^ D.ell j) (by positivity)
      (by intro I hI; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI; exact p.property.ne_zero)
      (by intro I hI; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI; exact hT j p hp)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective, mul_assoc] using hh
  rw [Fintype.card_pi, Nat.cast_prod]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∏j, 128 * b * Z ^ D.ell j :=
      Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => hc j)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← Real.rpow_sum_of_pos hZ, hsum]

/-- Exact new total-E cost; the original 13/2 exponent misses 3*rho0. -/
theorem same_D_canonical_contour_cost {Delta : ℝ} (D : HighDataPerturbed Delta)
    (eta : Character) (u : FreeRow) (P : Fin D.N → PrimeIdeal)
    (Z b : ℝ) (hZ : 1 ≤ Z) (hb : 0 ≤ b)
    (hu : ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ≤ Z ^ (physicalHeight + D.t))
    (hP : ∀j, ((P j).val.absNorm : ℝ) ≤ b * Z ^ D.ell j) :
    contourArithmeticCost eta u P ≤
      (eta.modulus.absNorm : ℝ) ^ 2 * (b ^ D.N) ^ 3 * Z ^ (13 / 2 + 3 * rho0) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hcap := same_D_height_cap D
  have ht := D.t_pos
  have hu' : ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ≤ Z :=
    hu.trans (by
      have hexp : physicalHeight + D.t ≤ (1 : ℝ) := by linarith
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ hexp)
  have hp := same_D_canonical_prime_product D P Z b hZ0 hP
  have hp0 : 0 ≤ ∏j, ((P j).val.absNorm : ℝ) :=
    Finset.prod_nonneg (fun j _ => Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (eta.modulus.absNorm : ℝ) ^ 2 * Z ^ 6 * (b ^ D.N * Z ^ totalE) ^ 3 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3)
        (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hZ0.le, ← Real.rpow_natCast Z 6]
      have hpowers : Z ^ (6 : ℝ) * Z ^ (totalE * (3 : ℕ)) =
          Z ^ (13 / 2 + 3 * rho0) := by
        rw [← Real.rpow_add hZ0]
        congr 1
        unfold totalE
        norm_num only [Nat.cast_ofNat]
        ring
      rw [← hpowers]
      norm_num only [Nat.cast_ofNat]
      ring

theorem shifted_canonical_crude_source_scale {Z a e : ℝ}
    (hZ : 1 ≤ Z) (ha : 0 ≤ a) (he : 0 ≤ e) :
    (Z ^ sourceLx) ^ (1 / 2 - (17 / 50 : ℝ)) * Z ^ (2 + (17 / 50 : ℝ) - 1) *
      (Z ^ sourceLy) ^ ((1 - a - 6 * e) - 1) ≤ Z ^ (2 : ℝ) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  simp_rw [← Real.rpow_mul hZ0.le]
  rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hx : sourceLx ≤ 1 := by norm_num [sourceLx, rho0]
  have hy := mul_nonpos_of_nonneg_of_nonpos sourceLy_nonneg
    (show (1 - a - 6 * e) - 1 ≤ 0 by linarith)
  nlinarith

end SevenEighths.PerturbedCanonicalLocalPrep
end
end OAI
