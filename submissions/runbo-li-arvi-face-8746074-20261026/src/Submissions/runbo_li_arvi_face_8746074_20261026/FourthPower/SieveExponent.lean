/- Copyright (c) 2026 Sil. Apache-2.0.
The exponent invariant and its concrete completed-row consequence.
The invariant is asymmetric; reciprocity supplies the other orientation.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.SievePoissonRecurrence
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.SieveDescent

set_option autoImplicit false
namespace Candidate.FourthPower.SieveExponent
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open SexticSieve SieveOperator SieveRanges SieveDescent

def exponentShape (α M N : ℝ) : ℝ := M+N^α+M^(5/6 : ℝ)*N^(1/3 : ℝ)

def HasExponent (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    theta M N ≤ C*(M*N)^ε*exponentShape α M N

def HasCompletedExponent (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 0 < M → 1 ≤ N →
    SieveRanges.lambda M N ≤ C*(M*N)^ε*(M^α+M^(1/6 : ℝ)*N)

theorem exponent_initial : HasExponent 2 := by
  intro ε hε
  refine ⟨QuadraticInitialBound.initialSieveConstant,QuadraticInitialBound.initialSieveConstant_pos,?_⟩
  intro M N hM hN
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hpow : 1 ≤ (M*N)^ε := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hM hN) hε.le
  have hC := QuadraticInitialBound.initialSieveConstant_pos
  have hshape : M+N^2 ≤ exponentShape 2 M N := by
    unfold exponentShape
    rw [Real.rpow_two]
    exact le_add_of_nonneg_right (by positivity)
  calc
    _ ≤ QuadraticInitialBound.initialSieveConstant*(M+N^2) := theta_initial M N hM hN
    _ ≤ QuadraticInitialBound.initialSieveConstant*exponentShape 2 M N :=
      mul_le_mul_of_nonneg_left hshape hC.le
    _ ≤ QuadraticInitialBound.initialSieveConstant*(M*N)^ε*exponentShape 2 M N := by
      apply mul_le_mul_of_nonneg_right _
        (show 0 ≤ exponentShape 2 M N by unfold exponentShape; positivity)
      exact le_mul_of_one_le_right hC.le hpow

theorem lambda_zero_of_lt_one (M N : ℝ) (hM : M < 1) : SieveRanges.lambda M N = 0 := by
  have he : SieveRanges.fullRange M = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨I,hI⟩
    have hh := SieveRanges.mem_fullRange.mp hI
    have hn := CenteredExceptionalCount.norm_one_le hh.1.1
    linarith
  apply le_antisymm _ (lambda_nonneg M N)
  change squaredNorm (SieveRanges.fullRange M) (freeRange N) ≤ 0
  rw [he]
  apply (bound_iff _ _ 0 le_rfl).mpr
  intro a
  simp [energy]

theorem mixed_le (α M N : ℝ) (hα : (7/6 : ℝ) ≤ α) (hM : 1 ≤ M) (hN : 0 < N) :
    M^(1/3 : ℝ)*N^(5/6 : ℝ) ≤ M^α+M^(1/6 : ℝ)*N := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  by_cases hn : N ≤ M
  · calc
      _ ≤ M^(1/3 : ℝ)*M^(5/6 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hN.le hn (by norm_num : (0 : ℝ) ≤ 5/6)) (by positivity)
      _ = M^(7/6 : ℝ) := by rw [← Real.rpow_add hM0]; norm_num
      _ ≤ M^α := Real.rpow_le_rpow_of_exponent_le hM hα
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have hmn : M ≤ N := le_of_not_ge hn
    have hsplit : M^(1/3 : ℝ)=M^(1/6 : ℝ)*M^(1/6 : ℝ) := by
      rw [← Real.rpow_add hM0]
      norm_num
    calc
      _ = M^(1/6 : ℝ)*(M^(1/6 : ℝ)*N^(5/6 : ℝ)) := by rw [hsplit]; ring
      _ ≤ M^(1/6 : ℝ)*(N^(1/6 : ℝ)*N^(5/6 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hM0.le hmn (by norm_num : (0 : ℝ) ≤ 1/6)) (by positivity)) (by positivity)
      _ = M^(1/6 : ℝ)*N := by rw [← Real.rpow_add hN]; norm_num
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

theorem root_power_term (M R p : ℝ) (hM : 0 < M) (hR : 1 ≤ R) (hp : 1 ≤ 6*p) :
    R*(M/R^6)^p ≤ M^p := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hr : R ≤ R^(6*p) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR hp
  have hrpos : 0 < R^(6*p) := Real.rpow_pos_of_pos hR0 _
  calc
    _ = M^p*(R/R^(6*p)) := by
      rw [Real.div_rpow hM.le (pow_nonneg hR0.le _),← Real.rpow_natCast_mul hR0.le,Nat.cast_ofNat]
      ring
    _ ≤ M^p*1 := mul_le_mul_of_nonneg_left ((div_le_one hrpos).mpr hr) (by positivity)
    _ = _ := mul_one _

theorem root_shape (α M N R : ℝ) (hα : (7/6 : ℝ) ≤ α)
    (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRhi : R ≤ M^(1/6 : ℝ)) :
    R*exponentShape α N (M/R^6) ≤ 2*(M^α+M^(1/6 : ℝ)*N) := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have h₁ := mul_le_mul_of_nonneg_right hRhi hN.le
  have h₂ := root_power_term M R α hM0 hR (by linarith)
  have h₃ := mul_le_mul_of_nonneg_right
    (root_power_term M R (1/3) hM0 hR (by norm_num)) (show 0 ≤ N^(5/6 : ℝ) by positivity)
  have h₄ := mixed_le α M N hα hM hN
  unfold exponentShape
  nlinarith

theorem completed_of_exponent (α : ℝ) (h : HasExponent α) (hα : (7/6 : ℝ) ≤ α) :
    HasCompletedExponent α := by
  intro ε hε
  have hδ : 0 < ε/2 := by positivity
  obtain ⟨C,hC,hb⟩ := h (ε/2) hδ
  let D := rootMass (1+ε/2)
  have hD : 0 ≤ D := rootMass_nonneg _
  refine ⟨512*C*(D+1),by positivity,?_⟩
  intro M N hM hN
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hZ : 0 ≤ M^α+M^(1/6 : ℝ)*N := by positivity
  by_cases hM1 : 1 ≤ M
  · obtain ⟨R,hR,hRhi,hscale,hd⟩ := lambda_scale_descent (ε/2) hδ M N hM1
    have hR0 : 0 < R := zero_lt_one.trans_le hR
    have hsmall : 0 < M/R^6 := zero_lt_one.trans_le hscale
    have hsmallM : M/R^6 ≤ M := div_le_self hM.le (one_le_pow₀ hR)
    have hT : 0 ≤ exponentShape α N (M/R^6) := by unfold exponentShape; positivity
    have htheta := (theta_reverse (M/R^6) N).trans
      (mul_le_mul_of_nonneg_left (hb N (M/R^6) hN hscale) (by norm_num : (0 : ℝ) ≤ 256))
    have hp₁ := Real.rpow_le_rpow (mul_nonneg hN0.le hsmall.le)
      (show N*(M/R^6) ≤ M*N from (mul_le_mul_of_nonneg_left hsmallM hN0.le).trans_eq (mul_comm N M)) hδ.le
    have hp₂ := Real.rpow_le_rpow hM.le (show M ≤ M*N from le_mul_of_one_le_right hM.le hN) hδ.le
    have hp : M^(ε/2)*(N*(M/R^6))^(ε/2) ≤ (M*N)^ε := by
      apply (mul_le_mul hp₂ hp₁ (by positivity) (by positivity)).trans_eq
      rw [← Real.rpow_add (mul_pos hM hN0)]
      congr 1
      ring
    have hshape := root_shape α M N R hα hM1 hN0 hR hRhi
    have htheta0 := theta_nonneg (M/R^6) N
    change SieveRanges.lambda M N ≤ D*M^(ε/2)*(R*theta (M/R^6) N) at hd
    calc
      _ ≤ D*M^(ε/2)*(R*theta (M/R^6) N) := hd
      _ ≤ (D+1)*M^(ε/2)*(R*theta (M/R^6) N) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right zero_le_one) (by positivity)) (by positivity)
      _ ≤ (D+1)*M^(ε/2)*(R*(256*(C*(N*(M/R^6))^(ε/2)*exponentShape α N (M/R^6)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htheta hR0.le) (by positivity)
      _ = 256*C*(D+1)*(M^(ε/2)*(N*(M/R^6))^(ε/2))*(R*exponentShape α N (M/R^6)) := by ring
      _ ≤ 256*C*(D+1)*(M*N)^ε*(2*(M^α+M^(1/6 : ℝ)*N)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hshape (by positivity) (by positivity)
      _ = _ := by ring
  · rw [lambda_zero_of_lt_one M N (lt_of_not_ge hM1)]
    positivity

theorem completed_initial : HasCompletedExponent 2 :=
  completed_of_exponent 2 exponent_initial (by norm_num)

end
end Candidate.FourthPower.SieveExponent
