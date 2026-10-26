/- Copyright (c) 2026 Sil. Apache-2.0.
The actual marked inverse (H-B) H^{-2}, including its frozen central factor.
Only finitely many labelled marked slots will be summed over the prime pool.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.KernelSeriesMass
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.KernelInverseIdealMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelInverseMarkedMass
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelFormal KernelMarkedMass KernelCoefficients KernelSeriesMass
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve SieveDescent
local notation "Id" => Ideal ActualEisensteinCubic.O

def markedSeries : LocalSeries :=
  (kernelSeries-LocalKernels.base formalX formalY)*reciprocalSeries^2

theorem marked_polynomial_expansion :
    LocalKernels.base formalX formalY-kernelSeries =
      ∑ i : Fin 14, MvPowerSeries.monomial
        (exponent (markedExponent i).1 (markedExponent i).2) (markedCoefficient i) := by
  rw [marked_series_expansion]
  apply Finset.sum_congr rfl
  intro i hi
  rw [formal_power_monomial,← map_zsmul,zsmul_eq_mul,mul_one]
  simp

theorem marked_polynomial_mass {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (weight (LocalKernels.base formalX formalY-kernelSeries) z) ∧
      (∑' n, weight (LocalKernels.base formalX formalY-kernelSeries) z n) ≤ 14*z := by
  rw [marked_polynomial_expansion]
  obtain ⟨hs,hb⟩ := finite_polynomial_mass markedCoefficient
    (fun i => exponent (markedExponent i).1 (markedExponent i).2) hz
  refine ⟨hs,hb.trans ?_⟩
  calc
    _ ≤ ∑ _i : Fin 14, z := by
      apply Finset.sum_le_sum
      intro i hi
      have hc : |(markedCoefficient i : ℝ)| = 1 := by
        fin_cases i <;> norm_num [markedCoefficient]
      have he : 1 ≤ degree (exponent (markedExponent i).1 (markedExponent i).2) := by
        fin_cases i <;> norm_num [degree_exponent,markedExponent]
      rw [hc,one_mul]
      simpa only [pow_one] using pow_le_pow_of_le_one hz hz1 he
    _ = _ := by simp

theorem weight_sub_rev (A B : LocalSeries) (z : ℝ) : weight (A-B) z = weight (B-A) z := by
  funext n
  simp only [weight,map_sub,Int.cast_sub,abs_sub_comm]

theorem reciprocal_mass_le_27 {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 2/5) :
    (∑' n, weight reciprocalSeries z n) ≤ 27 := by
  have hc := pow_le_pow_left₀ hz hz1 3
  have hb := reciprocal_mass hz hz1
  norm_num at hc
  linarith

/-- No inverse coefficient is omitted: the infinite marked series is absolutely summable. -/
theorem marked_inverse_mass {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 2/5) :
    Summable (weight markedSeries z) ∧
      (∑' n, weight markedSeries z n) ≤ 10206*z := by
  have hp := marked_polynomial_mass hz (show z ≤ 1 by linarith)
  have hP : Summable (weight (kernelSeries-LocalKernels.base formalX formalY) z) := by
    rw [weight_sub_rev]
    exact hp.1
  have hPb : (∑' n, weight (kernelSeries-LocalKernels.base formalX formalY) z n) ≤ 14*z := by
    rw [weight_sub_rev]
    exact hp.2
  have hI := reciprocal_summable hz hz1
  have hIb := reciprocal_mass_le_27 hz hz1
  have hII := mass_mul reciprocalSeries reciprocalSeries hz hI hI
  have hM := mass_mul (kernelSeries-LocalKernels.base formalX formalY)
    (reciprocalSeries*reciprocalSeries) hz hP hII.1
  have hIn : 0 ≤ ∑' n, weight reciprocalSeries z n := tsum_nonneg (weight_nonneg _ hz)
  have hIIn : 0 ≤ ∑' n, weight (reciprocalSeries*reciprocalSeries) z n :=
    tsum_nonneg (weight_nonneg _ hz)
  have hIIb : (∑' n, weight (reciprocalSeries*reciprocalSeries) z n) ≤ 729 := by
    nlinarith [hII.2]
  refine ⟨by simpa only [markedSeries,pow_two] using hM.1,?_⟩
  calc
    _ ≤ (∑' n, weight (kernelSeries-LocalKernels.base formalX formalY) z n)*
        (∑' n, weight (reciprocalSeries*reciprocalSeries) z n) := by
      simpa only [markedSeries,pow_two] using hM.2
    _ ≤ (14*z)*729 := mul_le_mul hPb hIIb hIIn (by positivity)
    _ = _ := by ring

def localMarkedMass (z : ℝ) (ij : ℕ × ℕ) : ℝ :=
  z*weight markedSeries z (exponent ij.1 ij.2)

theorem localMarkedMass_nonneg {z : ℝ} (hz : 0 ≤ z) (ij : ℕ × ℕ) :
    0 ≤ localMarkedMass z ij := mul_nonneg hz (weight_nonneg _ hz _)

theorem local_marked_mass_finite (T : Finset (ℕ × ℕ)) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 2/5) :
    (∑ ij ∈ T, localMarkedMass z ij) ≤ 10206*z^2 := by
  have hm := marked_inverse_mass hz hz1
  have hs : Summable (fun ij : ℕ × ℕ => weight markedSeries z (exponent ij.1 ij.2)) := by
    change Summable (weight markedSeries z ∘ pairExponent)
    exact (pairExponent.summable_iff (f := weight markedSeries z)).mpr hm.1
  have htotal : (∑' ij : ℕ × ℕ, weight markedSeries z (exponent ij.1 ij.2)) ≤ 10206*z := by
    change (∑' ij : ℕ × ℕ, weight markedSeries z (pairExponent ij)) ≤ 10206*z
    rw [pairExponent.tsum_eq (weight markedSeries z)]
    exact hm.2
  have hf := (Summable.sum_le_tsum T (fun ij _ => weight_nonneg _ hz _) hs).trans htotal
  calc
    _ = z*∑ ij ∈ T, weight markedSeries z (exponent ij.1 ij.2) := (Finset.mul_sum _ _ _).symm
    _ ≤ z*(10206*z) := mul_le_mul_of_nonneg_left hf hz
    _ = _ := by ring

theorem prime_marked_mass (P : PrimeIdeal) (hP : Supported P.val) (T : Finset (ℕ × ℕ)) :
    (∑ ij ∈ T, localMarkedMass ((Ideal.absNorm P.val : ℝ)^(-(1/2 : ℝ))) ij) ≤
      10206*(Ideal.absNorm P.val : ℝ)⁻¹ := by
  have hp : (7 : ℝ) ≤ Ideal.absNorm P.val := by
    exact_mod_cast KernelInverseIdealMass.supported_prime_norm P hP
  have hp0 : (0 : ℝ) < Ideal.absNorm P.val := by linarith
  have hh := local_marked_mass_finite T (Real.rpow_nonneg hp0.le (-(1/2 : ℝ)))
    (KernelInverseIdealMass.central_radius hp)
  have he : ((Ideal.absNorm P.val : ℝ)^(-(1/2 : ℝ)))^2 =
      (Ideal.absNorm P.val : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hp0.le]
    norm_num [Real.rpow_neg_one]
  simpa only [he] using hh

end
end Candidate.FourthPower.KernelInverseMarkedMass
