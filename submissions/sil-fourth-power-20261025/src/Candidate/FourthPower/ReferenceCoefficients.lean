/- Copyright (c) 2026 Sil. Apache-2.0.
Central normalization of actual smooth Hecke factors, with common frequency
phases, and of their full finite convolutions. Natural character zeros remain.
-/
import Candidate.FourthPower.ReferenceConvolution
import Candidate.FourthPower.KernelRowPools
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge

set_option autoImplicit false
namespace Candidate.FourthPower.ReferenceCoefficients
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic HeckeFamily
open CenteredMomentComparisonReflection HeckeDetectorDyadicBridge
open ReferenceConvolution
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]

theorem product_norm (v : α → Id) :
    (Ideal.absNorm (product v) : ℝ) = ∏ i, (Ideal.absNorm (v i) : ℝ) := by
  simp only [product,map_prod,Nat.cast_prod]

theorem sqrt_product_norm (v : α → Id) :
    Real.sqrt (Ideal.absNorm (product v) : ℝ) = ∏ i, Real.sqrt (Ideal.absNorm (v i) : ℝ) := by
  simp_rw [Real.sqrt_eq_rpow]
  rw [Real.finsetProd_rpow _ _ (fun i _ => Nat.cast_nonneg _),product_norm]

theorem product_coefficient_bound (a : α → Id → ℂ) (B : α → ℝ)
    (hB : ∀ i, 0 ≤ B i) (v : α → Id)
    (ha : ∀ i, ‖a i (v i)‖ ≤ B i/Real.sqrt (Ideal.absNorm (v i) : ℝ)) :
    ‖∏ i, a i (v i)‖ ≤ (∏ i, B i)/Real.sqrt (Ideal.absNorm (product v) : ℝ) := by
  rw [norm_prod,sqrt_product_norm,← Finset.prod_div_distrib]
  exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ha i)

theorem product_length_bound (v : α → Id) (H : α → ℝ)
    (hH : ∀ i, (Ideal.absNorm (v i) : ℝ) ≤ H i) :
    (Ideal.absNorm (product v) : ℝ) ≤ ∏ i, H i := by
  rw [product_norm]
  exact Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hH i)

def phaseCoefficient (W : ℝ → ℂ) (X v : ℝ) (I : Id) : ℂ :=
  (Real.sqrt X : ℂ)⁻¹*W ((Ideal.absNorm I : ℝ)/X)*
    FourierBridge.logPhase v (Real.log ((Ideal.absNorm I : ℝ)/X))

theorem phase_polynomial_finite (χ : Character) (W : ℝ → ℂ) (X v : ℝ)
    (hX : 0 < X) (S : Finset Id) (hS : ∀ I ∈ S, I ≠ 0)
    (hc : ∀ I : Id, I ≠ 0 → W ((Ideal.absNorm I : ℝ)/X) ≠ 0 → I ∈ S) :
    HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*v) =
      ∑ I ∈ S, phaseCoefficient W X v I*idealCoeff χ I := by
  rw [polynomial_eq_finite χ false W X 0 (2*Real.pi*v) S hc,
    inverse_half_power X hX.le,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hi
  have hn : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hi))
  have hp := norm_phase (Ideal.absNorm I : ℝ) X hn hX 0 v
  simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hp
  rw [← hp]
  simp only [HeckeDyadic.coefficient,Bool.false_eq_true,ite_false,phaseCoefficient]
  ring

/-- The frequency contributes unit modulus; the normalization is by the
original length X, not by the ideal norm. Support pays precisely sqrt(b). -/
theorem phase_coefficient_bound (W : ℝ → ℂ) (X v b B : ℝ)
    (hX : 0 < X) (hb : 0 ≤ b) (hB : 0 ≤ B) (I : Id) (hI : I ≠ 0)
    (hcap : (Ideal.absNorm I : ℝ) ≤ b*X) (hW : ‖W ((Ideal.absNorm I : ℝ)/X)‖ ≤ B) :
    ‖phaseCoefficient W X v I‖ ≤ (Real.sqrt b*B)/Real.sqrt (Ideal.absNorm I : ℝ) := by
  have hN : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hs : Real.sqrt (Ideal.absNorm I : ℝ) ≤ Real.sqrt b*Real.sqrt X := by
    simpa only [Real.sqrt_mul hb] using Real.sqrt_le_sqrt hcap
  have hi : (Real.sqrt X)⁻¹ ≤ Real.sqrt b/Real.sqrt (Ideal.absNorm I : ℝ) := by
    rw [inv_eq_one_div]
    exact (div_le_div_iff₀ (Real.sqrt_pos.mpr hX) (Real.sqrt_pos.mpr hN)).mpr (by simpa using hs)
  rw [phaseCoefficient,norm_mul,FourierBridge.logPhase_norm,mul_one,norm_mul,
    norm_inv,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg X)]
  calc
    _ ≤ (Real.sqrt X)⁻¹*B := mul_le_mul_of_nonneg_left hW (inv_nonneg.mpr (Real.sqrt_nonneg X))
    _ ≤ (Real.sqrt b/Real.sqrt (Ideal.absNorm I : ℝ))*B := mul_le_mul_of_nonneg_right hi hB
    _ = _ := by ring

/-- Common fixed twists and punctures may be included in a coefficient.
No dependence on the variable sieve row is introduced by this operation. -/
theorem masked_product_bound (a : α → Id → ℂ) (B : α → ℝ)
    (hB : ∀ i, 0 ≤ B i) (mask : (α → Id) → ℂ) (v : α → Id)
    (hm : ‖mask v‖ ≤ 1)
    (ha : ∀ i, ‖a i (v i)‖ ≤ B i/Real.sqrt (Ideal.absNorm (v i) : ℝ)) :
    ‖mask v*(∏ i, a i (v i))‖ ≤ (∏ i, B i)/Real.sqrt (Ideal.absNorm (product v) : ℝ) := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hm).trans (product_coefficient_bound a B hB v ha)

end
end Candidate.FourthPower.ReferenceCoefficients
