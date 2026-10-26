/- Copyright (c) 2026 Sil. Apache-2.0.
The precise fractional cost after shortening both ordinary factors.
The central scalar and the shortened volume together give exponent 1-alpha,
not 1/2-alpha. This is the summable mass needed for alpha=7/10.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.PrincipalKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace Candidate.FourthPower.PrincipalExtraction
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAllocationIdentity KernelRowProfiles KernelSelectedMass
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem shorter_lower_bound (L X d e : ℝ) (hL : 0 ≤ L) (hLX : L ≤ X)
    (hd : 1 ≤ d) (he : 1 ≤ e) : L/(d*e) ≤ X/d := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have he0 : 0 < e := zero_lt_one.trans_le he
  rw [div_mul_eq_div_div]
  exact (div_le_self (div_nonneg hL hd0.le) he).trans
    (div_le_div_of_nonneg_right hLX hd0.le)

theorem central_shortened_volume (T n : ℝ) (hT : 0 ≤ T) (hn : 0 < n) :
    (Real.sqrt n)⁻¹*Real.sqrt (T/n)=Real.sqrt T/n := by
  rw [Real.sqrt_div hT]
  calc
    _ = Real.sqrt T/(Real.sqrt n*Real.sqrt n) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hn.le]

theorem fractional_cost (T L n α : ℝ) (hT : 0 ≤ T) (hL : 0 < L) (hn : 0 < n) :
    (Real.sqrt n)⁻¹*Real.sqrt (T/n)*(L/n)^(-α) =
      n^(-(1-α))*Real.sqrt T*L^(-α) := by
  rw [central_shortened_volume T n hT hn,Real.div_rpow hL.le hn.le,
    Real.rpow_neg hn.le,div_inv_eq_mul]
  have he : n⁻¹*n^α=n^(-(1-α)) := by
    rw [← Real.rpow_neg_one,← Real.rpow_add hn]
    congr 1
    ring
  calc
    _ = (n⁻¹*n^α)*Real.sqrt T*L^(-α) := by ring
    _ = _ := by rw [he]

theorem pair_weight (S : Finset PrimeIdeal) (A : S → LocalSeries) (σ : ℝ)
    (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) :
    idealWeight S A σ σ d = |(kernelOn S A d.1 d.2 : ℝ)| * (pairNorm d)^(-σ) := by
  have hi := (ideal_norm_one_le hd.1).trans' zero_le_one
  have hj := (ideal_norm_one_le hd.2).trans' zero_le_one
  unfold idealWeight pairNorm normWeight
  rw [Real.mul_rpow hi hj]
  ring

theorem actual_scalar_cost (χ : Character) (S : Finset PrimeIdeal) (A : S → LocalSeries)
    (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (T L α : ℝ) (hT : 0 ≤ T) (hL : 0 < L) :
    ‖extractedScalar χ (fun e => (kernelOn S A e.1 e.2 : ℂ)) d‖*
        Real.sqrt (T/pairNorm d)*(L/pairNorm d)^(-α) ≤
      idealWeight S A (1-α) (1-α) d*Real.sqrt T*L^(-α) := by
  have hn := pairNorm_pos hd.1 hd.2
  have hh := extractedScalar_bound χ (fun e => (kernelOn S A e.1 e.2 : ℂ)) d
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg _)) (Real.rpow_nonneg (by positivity) _)).trans_eq
  rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs,div_eq_mul_inv,pair_weight S A (1-α) d hd]
  calc
    _ = |(kernelOn S A d.1 d.2 : ℝ)| *
        ((Real.sqrt (pairNorm d))⁻¹*Real.sqrt (T/pairNorm d)*(L/pairNorm d)^(-α)) := by ring
    _ = _ := by rw [fractional_cost T L (pairNorm d) α hT hL hn]; ring

/-- Explicit transfer lemma, not an assumed analytic estimate. The child
inequality must be supplied for the actual equal-product ordinary rows. -/
theorem sum_bound (χ : Character) (S : Finset PrimeIdeal) (A : S → LocalSeries)
    (D : Finset (Id × Id)) (hd : ∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (G : (Id × Id) → ℂ) (T L α C M : ℝ)
    (hT : 0 ≤ T) (hL : 0 < L) (hC : 0 ≤ C)
    (hmass : (∑ d ∈ D, idealWeight S A (1-α) (1-α) d) ≤ M)
    (hG : ∀ d ∈ D, ‖G d‖ ≤ C*Real.sqrt (T/pairNorm d)*(L/pairNorm d)^(-α)) :
    ‖∑ d ∈ D, extractedScalar χ (fun e => (kernelOn S A e.1 e.2 : ℂ)) d*G d‖ ≤
      C*M*Real.sqrt T*L^(-α) := by
  calc
    _ ≤ ∑ d ∈ D, ‖extractedScalar χ (fun e => (kernelOn S A e.1 e.2 : ℂ)) d*G d‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ D, C*(idealWeight S A (1-α) (1-α) d*Real.sqrt T*L^(-α)) := by
      apply Finset.sum_le_sum
      intro d hD
      rw [norm_mul]
      calc
        _ ≤ ‖extractedScalar χ (fun e => (kernelOn S A e.1 e.2 : ℂ)) d‖*
            (C*Real.sqrt (T/pairNorm d)*(L/pairNorm d)^(-α)) :=
          mul_le_mul_of_nonneg_left (hG d hD) (norm_nonneg _)
        _ = C*(‖extractedScalar χ (fun e => (kernelOn S A e.1 e.2 : ℂ)) d‖*
            Real.sqrt (T/pairNorm d)*(L/pairNorm d)^(-α)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (actual_scalar_cost χ S A d (hd d hD) T L α hT hL) hC
    _ = C*(∑ d ∈ D, idealWeight S A (1-α) (1-α) d)*Real.sqrt T*L^(-α) := by
      simp only [← Finset.sum_mul,← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hC) (Real.sqrt_nonneg _)) (by positivity)

end
end Candidate.FourthPower.PrincipalExtraction
