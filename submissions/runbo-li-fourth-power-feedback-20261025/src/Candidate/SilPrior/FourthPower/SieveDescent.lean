/- Copyright (c) 2026 Sil. Apache-2.0.
Quantitative control of the sixth roots in the exact completed-norm descent.
This module uses actual finite norm functions, without an optimal-sieve input. -/
import Candidate.SilPrior.FourthPower.SieveRanges

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.SieveDescent
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open CenteredExceptionalCount SexticSieve SixthDecomposition SieveRanges
local notation "Id" => Ideal ActualEisensteinCubic.O

def roots (A : ℝ) : Finset Id := (SieveRanges.fullRange A).image sixthQuotient

theorem roots_supported {A : ℝ} {D : Id} (hD : D ∈ roots A) : Supported D := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hD
  exact quotient_supported I (SieveRanges.mem_fullRange.mp hI).1

theorem root_power_le {A : ℝ} {D : Id} (hD : D ∈ roots A) :
    (Ideal.absNorm D : ℝ)^6 ≤ A := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hD
  have hi := SieveRanges.mem_fullRange.mp hI
  have he := sixth_normal_form_norm I hi.1.1
  have hr := norm_one_le (sixthRemainder_ne_zero I)
  nlinarith [pow_nonneg (Nat.cast_nonneg (Ideal.absNorm (sixthQuotient I)) : (0:ℝ) ≤ _) 6]

theorem root_norm_le {A : ℝ} (hA : 0 ≤ A) {D : Id} (hD : D ∈ roots A) :
    (Ideal.absNorm D : ℝ) ≤ A^(1/6 : ℝ) := by
  have hp : (Ideal.absNorm D : ℝ)^(6 : ℝ) ≤ A := by
    simpa using root_power_le hD
  simpa only [one_div] using
    (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) hA (by norm_num : (0:ℝ)<6)).mpr hp

theorem root_scale_one {A : ℝ} {D : Id} (hD : D ∈ roots A) :
    1 ≤ A/(Ideal.absNorm D : ℝ)^6 := by
  exact (le_div_iff₀ (pow_pos (norm_pos (roots_supported hD).1) 6)).mpr
    (by simpa using root_power_le hD)

theorem roots_card (A : ℝ) (hA : 1 ≤ A) :
    ((roots A).card : ℝ) ≤ 128*A^(1/6 : ℝ) := by
  exact DescentFiberCost.finite_ideal_count_real _ _
    (Real.one_le_rpow hA (by norm_num))
    (fun D hD => (roots_supported hD).1)
    (fun D hD => root_norm_le (zero_le_one.trans hA) hD)

def rootMass (σ : ℝ) : ℝ :=
  ∑' D : {I : Id // Supported I}, (Ideal.absNorm D.val : ℝ)^(-σ)

theorem rootMass_nonneg (σ : ℝ) : 0 ≤ rootMass σ :=
  tsum_nonneg (fun D => Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem finite_root_mass (σ : ℝ) (hσ : 1 < σ) (F : Finset Id)
    (hF : ∀ D ∈ F, Supported D) :
    (∑ D ∈ F, (Ideal.absNorm D : ℝ)^(-σ)) ≤ rootMass σ := by
  let f : F → {I : Id // Supported I} := fun D => ⟨D.val,hF D.val D.property⟩
  have hf : Function.Injective f := fun D E h =>
    Subtype.ext (show D.val = E.val from congrArg (fun D : {I : Id // Supported I} => D.val) h)
  have h := (root_weight_summable σ hσ).sum_le_tsum (Finset.univ.image f)
    (fun D _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [Finset.sum_image (fun _ _ _ _ h => hf h)] at h
  rw [← Finset.sum_coe_sort]
  simpa only [rootMass, f] using h

/-- A finite quantitative descent retaining every sixth root and its true scale. -/
theorem lambda_envelope (A B C : ℝ) (f : ℝ → ℝ)
    (hf : ∀ D ∈ roots A, theta (A/(Ideal.absNorm D : ℝ)^6) B ≤ C*f (Ideal.absNorm D)) :
    lambda A B ≤ C*∑ D ∈ roots A, f (Ideal.absNorm D) := by
  apply (lambda_sixth_extraction A B).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum hf

/-- A quantitative single-scale descent. The harmless A^ε replaces the
dyadic partition by a convergent ideal weight. The selected R is an actual
sixth-root norm, and the smaller row scale remains at least one. -/
theorem lambda_scale_descent (ε : ℝ) (hε : 0 < ε) (A B : ℝ) (hA : 1 ≤ A) :
    ∃ R : ℝ, 1 ≤ R ∧ R ≤ A^(1/6 : ℝ) ∧ 1 ≤ A/R^6 ∧
      lambda A B ≤ rootMass (1+ε)*A^ε * (R*theta (A/R^6) B) := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  by_cases hn : (roots A).Nonempty
  · obtain ⟨D,hD,hmax⟩ := Finset.exists_max_image (roots A)
      (fun E => (Ideal.absNorm E : ℝ)*theta (A/(Ideal.absNorm E : ℝ)^6) B) hn
    let M : ℝ := (Ideal.absNorm D : ℝ)*theta (A/(Ideal.absNorm D : ℝ)^6) B
    have hM : 0 ≤ M := mul_nonneg (Nat.cast_nonneg _) (theta_nonneg _ _)
    refine ⟨Ideal.absNorm D,norm_one_le (roots_supported hD).1,
      root_norm_le hA0.le hD,root_scale_one hD,?_⟩
    have hb (E : Id) (hE : E ∈ roots A) :
        theta (A/(Ideal.absNorm E : ℝ)^6) B ≤
          (A^ε*M)*(Ideal.absNorm E : ℝ)^(-(1+ε)) := by
      have he0 := norm_pos (roots_supported hE).1
      have hEA : (Ideal.absNorm E : ℝ) ≤ A := by
        obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hE
        have hi := SieveRanges.mem_fullRange.mp hI
        exact (norm_le_of_dvd hi.1.1
          ((dvd_pow_self _ (by decide : (6:ℕ)≠0)).trans
            ⟨sixthRemainder I, by rw [mul_comm,sixth_normal_form I hi.1.1]⟩)).trans hi.2
      have hr : (Ideal.absNorm E : ℝ)^ε ≤ A^ε :=
        Real.rpow_le_rpow he0.le hEA hε.le
      have hi : theta (A/(Ideal.absNorm E : ℝ)^6) B =
          ((Ideal.absNorm E : ℝ)^ε *
            ((Ideal.absNorm E : ℝ)*theta (A/(Ideal.absNorm E : ℝ)^6) B)) *
          (Ideal.absNorm E : ℝ)^(-(1+ε)) := by
        rw [Real.rpow_neg he0.le, Real.rpow_add he0, Real.rpow_one]
        field_simp
      rw [hi]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hr (hmax E hE)
          (mul_nonneg he0.le (theta_nonneg _ _)) (Real.rpow_nonneg hA0.le _))
        (Real.rpow_nonneg he0.le _)
    calc
      lambda A B ≤ (A^ε*M)*∑ E ∈ roots A, (Ideal.absNorm E : ℝ)^(-(1+ε)) :=
        lambda_envelope A B (A^ε*M) (fun x => x^(-(1+ε))) hb
      _ ≤ (A^ε*M)*rootMass (1+ε) :=
        mul_le_mul_of_nonneg_left
          (finite_root_mass (1+ε) (by linarith) (roots A) (fun E hE => roots_supported hE))
          (mul_nonneg (Real.rpow_nonneg hA0.le _) hM)
      _ = _ := by dsimp [M]; ring
  · have he : roots A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    refine ⟨1,le_rfl,Real.one_le_rpow hA (by norm_num),by simpa using hA,?_⟩
    have hz : lambda A B ≤ 0 := by
      have h := lambda_sixth_extraction A B
      change lambda A B ≤ ∑ D ∈ roots A, theta (A/(Ideal.absNorm D : ℝ)^6) B at h
      simpa only [he,Finset.sum_empty] using h
    exact hz.trans (mul_nonneg
      (mul_nonneg (rootMass_nonneg _) (Real.rpow_nonneg hA0.le _))
      (mul_nonneg zero_le_one (theta_nonneg _ _)))

end
end Candidate.SilPrior.FourthPower.SieveDescent
