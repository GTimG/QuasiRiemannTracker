/- Copyright (c) 2026 Sil. Apache-2.0.
The completed-row reference majorant, with sixth powers and natural masks.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.SieveOptimal

set_option autoImplicit false
namespace Candidate.FourthPower.SieveReference
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open SexticSieve SieveOperator SieveRanges SieveDescent SieveExponent SieveOptimal
local notation "Id" => Ideal ActualEisensteinCubic.O

def referenceMajorant (M N : ℝ) : ℝ :=
  M+M^(1/6 : ℝ)*N+M^(5/6 : ℝ)*N^(1/3 : ℝ)+M^(1/3 : ℝ)*N^(5/6 : ℝ)

theorem referenceMajorant_nonneg (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N) :
    0 ≤ referenceMajorant M N := by unfold referenceMajorant; positivity

theorem referenceMajorant_ge_one (M N : ℝ) (hM : 1 ≤ M) (hN : 0 ≤ N) :
    1 ≤ referenceMajorant M N := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  unfold referenceMajorant
  have h₁ : 0 ≤ M^(1/6 : ℝ)*N := by positivity
  have h₂ : 0 ≤ M^(5/6 : ℝ)*N^(1/3 : ℝ) := by positivity
  have h₃ : 0 ≤ M^(1/3 : ℝ)*N^(5/6 : ℝ) := by positivity
  linarith

theorem root_reference (M N R : ℝ) (hM : 0 < M) (hN : 0 < N)
    (hR : 1 ≤ R) (hRhi : R ≤ M^(1/6 : ℝ)) :
    R*majorant (M/R^6) N ≤ referenceMajorant M N := by
  have h₁ := root_power_term M R 1 hM hR (by norm_num)
  rw [Real.rpow_one,Real.rpow_one] at h₁
  have h₂ := mul_le_mul_of_nonneg_right hRhi hN.le
  have h₃ := mul_le_mul_of_nonneg_right
    (root_power_term M R (5/6) hM hR (by norm_num)) (show 0 ≤ N^(1/3 : ℝ) by positivity)
  have h₄ := mul_le_mul_of_nonneg_right
    (root_power_term M R (1/3) hM hR (by norm_num)) (show 0 ≤ N^(5/6 : ℝ) by positivity)
  unfold majorant referenceMajorant
  nlinarith

/-- No power-free condition remains on the row ideal; the sixth-power
extraction retains the original common coefficients and coprimality masks. -/
theorem lambda_reference (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      SieveRanges.lambda M N ≤ C*(M*N)^ε*referenceMajorant M N := by
  have hδ : 0 < ε/2 := by positivity
  obtain ⟨C,hC,hb⟩ := theta_optimal (ε/2) hδ
  let D := rootMass (1+ε/2)
  have hD : 0 ≤ D := rootMass_nonneg _
  refine ⟨C*(D+1),by positivity,?_⟩
  intro M N hM hN
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  obtain ⟨R,hR,hRhi,hscale,hd⟩ := lambda_scale_descent (ε/2) hδ M N hM
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hsmall : 0 < M/R^6 := zero_lt_one.trans_le hscale
  have hsmallM : M/R^6 ≤ M := div_le_self hM0.le (one_le_pow₀ hR)
  have htheta := hb (M/R^6) N hscale hN
  have htheta0 := theta_nonneg (M/R^6) N
  have hmaj : 0 ≤ majorant (M/R^6) N := by unfold majorant; positivity
  have hp₁ := Real.rpow_le_rpow (mul_nonneg hsmall.le hN0.le)
    (mul_le_mul_of_nonneg_right hsmallM hN0.le) hδ.le
  have hp₂ := Real.rpow_le_rpow hM0.le (le_mul_of_one_le_right hM0.le hN) hδ.le
  have hp : M^(ε/2)*((M/R^6)*N)^(ε/2) ≤ (M*N)^ε := by
    apply (mul_le_mul hp₂ hp₁ (by positivity) (by positivity)).trans_eq
    rw [← Real.rpow_add (mul_pos hM0 hN0)]
    congr 1
    ring
  change SieveRanges.lambda M N ≤ D*M^(ε/2)*(R*theta (M/R^6) N) at hd
  calc
    _ ≤ D*M^(ε/2)*(R*theta (M/R^6) N) := hd
    _ ≤ (D+1)*M^(ε/2)*(R*theta (M/R^6) N) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)) (by positivity)
    _ ≤ (D+1)*M^(ε/2)*(R*(C*((M/R^6)*N)^(ε/2)*majorant (M/R^6) N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htheta hR0.le) (by positivity)
    _ = C*(D+1)*(M^(ε/2)*((M/R^6)*N)^(ε/2))*(R*majorant (M/R^6) N) := by ring
    _ ≤ C*(D+1)*(M*N)^ε*referenceMajorant M N :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity))
        (root_reference M N R hM0 hN0 hR hRhi) (by positivity) (by positivity)

theorem energy_le_lambda (M N : ℝ) (rows columns : Finset Id)
    (hr : ∀ R ∈ rows, Supported R ∧ (Ideal.absNorm R : ℝ) ≤ M)
    (hc : ∀ I ∈ columns, Supported I ∧ PowerFree 6 I ∧ (Ideal.absNorm I : ℝ) ≤ N)
    (a : Id → ℂ) : energy rows columns a ≤ SieveRanges.lambda M N*coefficientMass columns a := by
  apply (energy_bound rows columns a).trans
  apply mul_le_mul_of_nonneg_right _ (coefficientMass_nonneg columns a)
  exact norm_mono (fun R hR => SieveRanges.mem_fullRange.mpr (hr R hR))
    (fun I hI => mem_freeRange.mpr (hc I hI))

theorem ideal_reference (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      ∀ rows columns : Finset Id,
      (∀ R ∈ rows, Supported R ∧ (Ideal.absNorm R : ℝ) ≤ M) →
      (∀ I ∈ columns, Supported I ∧ PowerFree 6 I ∧ (Ideal.absNorm I : ℝ) ≤ N) →
      ∀ a : Id → ℂ, energy rows columns a ≤ C*(M*N)^ε*referenceMajorant M N*coefficientMass columns a := by
  obtain ⟨C,hC,hb⟩ := lambda_reference ε hε
  refine ⟨C,hC,?_⟩
  intro M N hM hN rows columns hr hc a
  exact (energy_le_lambda M N rows columns hr hc a).trans
    (mul_le_mul_of_nonneg_right (hb M N hM hN) (coefficientMass_nonneg columns a))

end
end Candidate.FourthPower.SieveReference
