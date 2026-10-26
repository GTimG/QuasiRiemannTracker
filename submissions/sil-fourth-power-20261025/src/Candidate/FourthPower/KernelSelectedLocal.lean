/- Copyright (c) 2026 Sil. Apache-2.0.
Local bounds for the actual forward and inverse marked kernels, suitable
for prime-dependent global mass. The ordinary and marked series stay distinct.
-/
import Candidate.FourthPower.KernelSelectedMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelSelectedLocal
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelFormal KernelForwardMass KernelMarkedMass KernelCoefficients KernelSelectedMass

theorem finite_table_mass {β : Type*} [Fintype β]
    (f : (ℕ × ℕ) → ℤ) (c : β → ℤ) (e : β → ℕ × ℕ)
    (hf : ∀ ij, f ij=∑ k : β, if ij=e k then c k else 0)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (T : Finset (ℕ × ℕ)) :
    (∑ ij ∈ T, |(f ij : ℝ)| *x^ij.1*y^ij.2) ≤
      ∑ k : β, |(c k : ℝ)| *x^(e k).1*y^(e k).2 := by
  have hp (ij : ℕ × ℕ) : |(f ij : ℝ)| ≤ ∑ k : β, if ij=e k then |(c k : ℝ)| else 0 := by
    rw [hf]
    push_cast
    apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
    exact Finset.sum_congr rfl (fun k _ => by split_ifs <;> simp)
  calc
    _ ≤ ∑ ij ∈ T, (∑ k : β, if ij=e k then |(c k : ℝ)| else 0)*x^ij.1*y^ij.2 :=
      Finset.sum_le_sum (fun ij _ => mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hp ij) (pow_nonneg hx _)) (pow_nonneg hy _))
    _ = ∑ k : β, ∑ ij ∈ T,
        if ij=e k then |(c k : ℝ)| *x^(e k).1*y^(e k).2 else 0 := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro ij _
      by_cases h : ij=e k <;> simp [h]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      rw [Finset.sum_ite_eq']
      split_ifs
      · exact le_rfl
      · positivity

theorem exponent_weight (p s t : ℝ) (hp : 0 < p) (ij : ℕ × ℕ) :
    (p^(-s))^ij.1*(p^(-t))^ij.2 = p^(-(s*ij.1+t*ij.2)) := by
  rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_mul hp.le,
    ← Real.rpow_mul hp.le,← Real.rpow_add hp]
  congr 1
  ring

theorem ordinary_local (P : PrimeIdeal) (s t u : ℝ)
    (hu : 0 ≤ u) (hs : u ≤ s) (ht : u ≤ t) (T : Finset (ℕ × ℕ)) :
    (∑ ij ∈ T, localWeight kernelSeries s t P ij) ≤
      1+11*(Ideal.absNorm P.val : ℝ)^(-(5*u)) := by
  have hp : (1 : ℝ) ≤ Ideal.absNorm P.val := ideal_norm_one_le P.property.ne_zero
  have hp0 : (0 : ℝ) < Ideal.absNorm P.val := zero_lt_one.trans_le hp
  have htable : ∀ ij : ℕ × ℕ, kernelCoeff (exponent ij.1 ij.2) =
      ∑ k : Fin 12, if ij=ordinaryExponent k then ordinaryCoefficient k else 0 := by
    intro ij
    rw [ordinary_coefficient_table]
    simp only [Prod.ext_iff]
  have hb := finite_table_mass (fun ij => kernelCoeff (exponent ij.1 ij.2))
    ordinaryCoefficient ordinaryExponent htable
    ((Ideal.absNorm P.val : ℝ)^(-s)) ((Ideal.absNorm P.val : ℝ)^(-t))
    (by positivity) (by positivity) T
  change (∑ ij ∈ T, localWeight kernelSeries s t P ij) ≤ _ at hb
  apply hb.trans
  rw [Fin.sum_univ_succ]
  have hz : |(ordinaryCoefficient 0 : ℝ)| *
      ((Ideal.absNorm P.val : ℝ)^(-s))^(ordinaryExponent 0).1 *
      ((Ideal.absNorm P.val : ℝ)^(-t))^(ordinaryExponent 0).2 = 1 := by
    norm_num [ordinaryCoefficient,ordinaryExponent]
  rw [hz]
  have hn : (∑ k : Fin 11, |(ordinaryCoefficient k.succ : ℝ)| *
      ((Ideal.absNorm P.val : ℝ)^(-s))^(ordinaryExponent k.succ).1 *
      ((Ideal.absNorm P.val : ℝ)^(-t))^(ordinaryExponent k.succ).2) ≤
      11*(Ideal.absNorm P.val : ℝ)^(-(5*u)) := by
    calc
      _ ≤ ∑ _k : Fin 11, (Ideal.absNorm P.val : ℝ)^(-(5*u)) := by
        apply Finset.sum_le_sum
        intro k _
        rw [KernelInverseCoefficients.nonconstant_abs,one_mul,exponent_weight _ s t hp0]
        apply Real.rpow_le_rpow_of_exponent_le hp
        have hj : 0 ≤ ((ordinaryExponent k.succ).1 : ℝ) := Nat.cast_nonneg _
        have hk : 0 ≤ ((ordinaryExponent k.succ).2 : ℝ) := Nat.cast_nonneg _
        have hdeg : (5 : ℝ) ≤ (ordinaryExponent k.succ).1+(ordinaryExponent k.succ).2 := by
          exact_mod_cast KernelInverseCoefficients.nonconstant_degree k
        nlinarith [mul_le_mul_of_nonneg_right hs hj,mul_le_mul_of_nonneg_right ht hk]
      _ = _ := by simp
  linarith

theorem marked_local (P : PrimeIdeal) (s t u : ℝ)
    (hu : 0 ≤ u) (hs : u ≤ s) (ht : u ≤ t) (T : Finset (ℕ × ℕ)) :
    (∑ ij ∈ T, localWeight (LocalKernels.base formalX formalY-kernelSeries) s t P ij) ≤
      14*(Ideal.absNorm P.val : ℝ)^(-u) := by
  have hp : (1 : ℝ) ≤ Ideal.absNorm P.val := ideal_norm_one_le P.property.ne_zero
  have hp0 : (0 : ℝ) < Ideal.absNorm P.val := zero_lt_one.trans_le hp
  have htable : ∀ ij : ℕ × ℕ,
      MvPowerSeries.coeff (exponent ij.1 ij.2) (LocalKernels.base formalX formalY-kernelSeries) =
        ∑ k : Fin 14, if ij=markedExponent k then markedCoefficient k else 0 := by
    intro ij
    rw [marked_coefficient_table]
    simp only [Prod.ext_iff]
  have hb := finite_table_mass
    (fun ij => MvPowerSeries.coeff (exponent ij.1 ij.2)
      (LocalKernels.base formalX formalY-kernelSeries))
    markedCoefficient markedExponent htable
    ((Ideal.absNorm P.val : ℝ)^(-s)) ((Ideal.absNorm P.val : ℝ)^(-t))
    (by positivity) (by positivity) T
  apply hb.trans
  calc
    _ ≤ ∑ _k : Fin 14, (Ideal.absNorm P.val : ℝ)^(-u) := by
      apply Finset.sum_le_sum
      intro k _
      have hc : |(markedCoefficient k : ℝ)|=1 := by fin_cases k <;> norm_num [markedCoefficient]
      rw [hc,one_mul,exponent_weight _ s t hp0]
      apply Real.rpow_le_rpow_of_exponent_le hp
      have hj : 0 ≤ ((markedExponent k).1 : ℝ) := Nat.cast_nonneg _
      have hk : 0 ≤ ((markedExponent k).2 : ℝ) := Nat.cast_nonneg _
      have hdeg : (1 : ℝ) ≤ (markedExponent k).1+(markedExponent k).2 := by
        fin_cases k <;> norm_num [markedExponent]
      nlinarith [mul_le_mul_of_nonneg_right hs hj,mul_le_mul_of_nonneg_right ht hk]
    _ = _ := by simp

theorem central_weight_eq (A : LocalSeries) (P : PrimeIdeal) (ij : ℕ × ℕ) :
    localWeight A (1/2) (1/2) P ij =
      KernelSeriesMass.weight A ((Ideal.absNorm P.val : ℝ)^(-(1/2 : ℝ))) (exponent ij.1 ij.2) := by
  simp only [localWeight,KernelSeriesMass.weight,degree_exponent,pow_add,mul_assoc]

theorem inverse_ordinary_local (P : PrimeIdeal) (hP : Supported P.val) (T : Finset (ℕ × ℕ)) :
    (∑ ij ∈ T, localWeight reciprocalSeries (1/2) (1/2) P ij) ≤
      1+400*(Ideal.absNorm P.val : ℝ)^(-(3/2 : ℝ)) := by
  convert KernelInverseIdealMass.local_central_mass P hP T using 1
  apply Finset.sum_congr rfl
  intro ij _
  simp [localWeight,KernelInverseMass.localMass,reciprocalCoeff,pow_add,mul_assoc]

theorem inverse_marked_local (P : PrimeIdeal) (hP : Supported P.val) (T : Finset (ℕ × ℕ)) :
    (∑ ij ∈ T, localWeight KernelInverseMarkedMass.markedSeries (1/2) (1/2) P ij) ≤
      10206*(Ideal.absNorm P.val : ℝ)^(-(1/2 : ℝ)) := by
  have hp : (7 : ℝ) ≤ Ideal.absNorm P.val := by
    exact_mod_cast KernelInverseIdealMass.supported_prime_norm P hP
  have hp0 : (0 : ℝ) < Ideal.absNorm P.val := by linarith
  have hm := KernelInverseMarkedMass.marked_inverse_mass
    (Real.rpow_nonneg hp0.le (-(1/2 : ℝ))) (KernelInverseIdealMass.central_radius hp)
  have hs := (KernelSeriesMass.pairExponent.summable_iff
    (f := KernelSeriesMass.weight KernelInverseMarkedMass.markedSeries
      ((Ideal.absNorm P.val : ℝ)^(-(1/2 : ℝ))))).mpr hm.1
  have hb := hs.sum_le_tsum T (fun ij _ => KernelSeriesMass.weight_nonneg _
    (Real.rpow_nonneg hp0.le (-(1/2 : ℝ))) (KernelSeriesMass.pairExponent ij))
  rw [KernelSeriesMass.pairExponent.tsum_eq] at hb
  change (∑ ij ∈ T, KernelSeriesMass.weight KernelInverseMarkedMass.markedSeries
    ((Ideal.absNorm P.val : ℝ)^(-(1/2 : ℝ))) (exponent ij.1 ij.2)) ≤ _ at hb
  simpa only [central_weight_eq] using hb.trans hm.2

end
end Candidate.FourthPower.KernelSelectedLocal
