/- Copyright (c) 2026 Joseph Bebel. -/
import Mathlib

/-!
# Finite inverse amplification

The source index `T` contains all products of an old source and an amplifier
monomial.  Its fibers are controlled by a multiplicity `D`; no squarefree
projection or extra factor equal to the number of monomials is used.
-/

namespace Qrh.JointDetector

open scoped BigOperators

/-- Coefficient Cauchy--Schwarz for a finite complex linear combination. -/
theorem coefficient_cauchy {I : Type*} [Fintype I] (c u : I → ℂ) :
    ‖∑ i, c i * u i‖ ^ 2 ≤
      (∑ i, ‖c i‖ ^ 2) * ∑ i, ‖u i‖ ^ 2 := by
  calc
    ‖∑ i, c i * u i‖ ^ 2 ≤ (∑ i, ‖c i * u i‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2
        (norm_sum_le _ _)
    _ = (∑ i, ‖c i‖ * ‖u i‖) ^ 2 := by simp only [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- An arbitrary merge map costs only the maximum fiber cardinality. -/
theorem merge_energy_bound {P T : Type*} [Fintype P] [Fintype T] [DecidableEq T]
    (merge : P → T) (u : T → ℂ) (D : ℝ)
    (hfiber : ∀ t, ((Finset.univ.filter fun p => merge p = t).card : ℝ) ≤ D) :
    ∑ p, ‖u (merge p)‖ ^ 2 ≤ D * ∑ t, ‖u t‖ ^ 2 := by
  classical
  calc
    ∑ p, ‖u (merge p)‖ ^ 2 =
        ∑ t, ∑ p ∈ Finset.univ.filter (fun p => merge p = t), ‖u t‖ ^ 2 := by
      symm
      exact Finset.sum_fiberwise_of_maps_to' (fun _ _ => Finset.mem_univ _) _
    _ = ∑ t, ((Finset.univ.filter fun p => merge p = t).card : ℝ) * ‖u t‖ ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ t, D * ‖u t‖ ^ 2 :=
      Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_right (hfiber t) (sq_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Finite inverse amplification with the full merged source family.

`fold r t` is the target feature, `old r n` the original feature, and `amp r m`
its amplifier feature. The only multiplicativity hypothesis is the displayed
product identity. The target dual energy hypothesis is required for *every*
complex row vector. The conclusion has cost `C * D * K / A`, without an
additional monomial-count factor.
-/
theorem inverse_amplification
    {R N M T : Type*} [Fintype R] [Fintype N] [Fintype M] [Fintype T] [DecidableEq T]
    (merge : N × M → T) (old : R → N → ℂ) (amp : R → M → ℂ)
    (fold : R → T → ℂ) (c : M → ℂ) (A C D K : ℝ)
    (hA : 0 < A) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hproduct : ∀ r n m, fold r (merge (n, m)) = old r n * amp r m)
    (hresponse : ∀ r, A ≤ ‖∑ m, c m * amp r m‖ ^ 2)
    (hcoeff : ∑ m, ‖c m‖ ^ 2 ≤ C)
    (hfiber : ∀ t, ((Finset.univ.filter fun p => merge p = t).card : ℝ) ≤ D)
    (htarget : ∀ z : R → ℂ,
      ∑ t, ‖∑ r, z r * fold r t‖ ^ 2 ≤ K * ∑ r, ‖z r‖ ^ 2)
    (z : R → ℂ) :
    ∑ n, ‖∑ r, z r * old r n‖ ^ 2 ≤
      C * D * K / A * ∑ r, ‖z r‖ ^ 2 := by
  classical
  let response : R → ℂ := fun r => ∑ m, c m * amp r m
  let z' : R → ℂ := fun r => z r / response r
  let u : T → ℂ := fun t => ∑ r, z' r * fold r t
  have hresponse' (r : R) : A ≤ ‖response r‖ ^ 2 := hresponse r
  have hne (r : R) : response r ≠ 0 := by
    intro hz
    have := hresponse' r
    simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    linarith
  have hid (n : N) : ∑ r, z r * old r n = ∑ m, c m * u (merge (n, m)) := by
    dsimp [u]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    simp_rw [hproduct]
    calc
      z r * old r n = (z' r * old r n) * response r := by
        dsimp [z']
        field_simp [hne r]
      _ = ∑ m, c m * (z' r * (old r n * amp r m)) := by
        dsimp [response]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
  have hmass : ∑ r, ‖z' r‖ ^ 2 ≤ (∑ r, ‖z r‖ ^ 2) / A := by
    calc
      ∑ r, ‖z' r‖ ^ 2 = ∑ r, ‖z r‖ ^ 2 / ‖response r‖ ^ 2 := by
        simp only [z', norm_div, div_pow]
      _ ≤ ∑ r, ‖z r‖ ^ 2 / A := by
        exact Finset.sum_le_sum fun r _ =>
          div_le_div_of_nonneg_left (sq_nonneg _) hA (hresponse' r)
      _ = _ := (Finset.sum_div _ _ _).symm
  have hmerge : ∑ n, ∑ m, ‖u (merge (n, m))‖ ^ 2 ≤ D * ∑ t, ‖u t‖ ^ 2 := by
    simpa only [Fintype.sum_prod_type] using merge_energy_bound merge u D hfiber
  calc
    ∑ n, ‖∑ r, z r * old r n‖ ^ 2 = ∑ n, ‖∑ m, c m * u (merge (n, m))‖ ^ 2 := by
      simp_rw [hid]
    _ ≤ ∑ n, C * ∑ m, ‖u (merge (n, m))‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n _
      exact (coefficient_cauchy c (fun m => u (merge (n, m)))).trans
        (mul_le_mul_of_nonneg_right hcoeff (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    _ = C * ∑ n, ∑ m, ‖u (merge (n, m))‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (D * ∑ t, ‖u t‖ ^ 2) := mul_le_mul_of_nonneg_left hmerge hC
    _ ≤ C * (D * (K * ∑ r, ‖z' r‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact mul_le_mul_of_nonneg_left (htarget z') hD
    _ ≤ C * (D * (K * ((∑ r, ‖z r‖ ^ 2) / A))) := by
      gcongr
    _ = _ := by ring

end Qrh.JointDetector

#print axioms Qrh.JointDetector.inverse_amplification
