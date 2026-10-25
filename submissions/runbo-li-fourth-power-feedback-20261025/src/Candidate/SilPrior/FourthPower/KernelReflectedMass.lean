/- Copyright (c) 2026 Sil. Apache-2.0.
Central forward mass and the actual reflected length-ratio cost.
The anisotropic mass has already been proved for the same ideal kernel.
-/
import Candidate.SilPrior.FourthPower.KernelSeriesMass
import Candidate.SilPrior.FourthPower.KernelIdealMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.KernelReflectedMass
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open KernelFormal KernelForwardMass KernelCoefficients KernelSeriesMass SieveDescent
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem ordinary_polynomial_expansion : kernelSeries = ∑ i : Fin 12,
    MvPowerSeries.monomial (exponent (ordinaryExponent i).1 (ordinaryExponent i).2)
      (ordinaryCoefficient i) := by
  rw [ordinary_series_expansion]
  apply Finset.sum_congr rfl
  intro i hi
  rw [formal_power_monomial,← map_zsmul,zsmul_eq_mul,mul_one]
  simp

theorem ordinary_central_mass {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (weight kernelSeries z) ∧ (∑' n, weight kernelSeries z n) ≤ 1+11*z^5 := by
  rw [ordinary_polynomial_expansion]
  obtain ⟨hs,hb⟩ := finite_polynomial_mass ordinaryCoefficient
    (fun i => exponent (ordinaryExponent i).1 (ordinaryExponent i).2) hz
  refine ⟨hs,hb.trans ?_⟩
  rw [Fin.sum_univ_succ]
  have hz0 : |(ordinaryCoefficient 0 : ℝ)| *
      z^(degree (exponent (ordinaryExponent 0).1 (ordinaryExponent 0).2)) = 1 := by
    norm_num [ordinaryCoefficient,ordinaryExponent,degree_exponent]
  rw [hz0]
  have hh : (∑ i : Fin 11, |(ordinaryCoefficient i.succ : ℝ)| *
      z^(degree (exponent (ordinaryExponent i.succ).1 (ordinaryExponent i.succ).2))) ≤ 11*z^5 := by
    calc
      _ ≤ ∑ _i : Fin 11, z^5 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [KernelInverseCoefficients.nonconstant_abs,one_mul,degree_exponent]
        exact pow_le_pow_of_le_one hz hz1 (KernelInverseCoefficients.nonconstant_degree i)
      _ = _ := by simp
  linarith

theorem ordinary_central_mass_finite (T : Finset (ℕ × ℕ)) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (∑ ij ∈ T, |(kernelCoeff (exponent ij.1 ij.2) : ℝ)| *z^(ij.1+ij.2)) ≤ 1+11*z^5 := by
  have hm := ordinary_central_mass hz hz1
  have hs := (pairExponent.summable_iff (f := weight kernelSeries z)).mpr hm.1
  have hb := hs.sum_le_tsum T (fun ij _ => weight_nonneg _ hz (pairExponent ij))
  rw [pairExponent.tsum_eq (weight kernelSeries z)] at hb
  have he : (fun ij : ℕ × ℕ => weight kernelSeries z (pairExponent ij)) =
      (fun ij => |(kernelCoeff (exponent ij.1 ij.2) : ℝ)| *z^(ij.1+ij.2)) := by
    funext ij
    simp [pairExponent,weight,kernelCoeff,degree_exponent]
  simpa only [Function.comp_def,he] using hb.trans hm.2

theorem local_central_bound (P : PrimeIdeal) (T : Finset (ℕ × ℕ)) :
    (∑ ij ∈ T, localMassTerm kernelCoeff (1/2) P ij) ≤
      1+11*(Ideal.absNorm P.val : ℝ)^(-(5/2 : ℝ)) := by
  have hp : (1 : ℝ) ≤ Ideal.absNorm P.val := by
    have hh := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (show 1 ≤ Ideal.absNorm P.val by omega)
  have hp0 : (0 : ℝ) < Ideal.absNorm P.val := zero_lt_one.trans_le hp
  have hz : (Ideal.absNorm P.val : ℝ)^(-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp (by norm_num)
  have hh := ordinary_central_mass_finite T (Real.rpow_nonneg hp0.le (-(1/2 : ℝ))) hz
  have he : ((Ideal.absNorm P.val : ℝ)^(-(1/2 : ℝ)))^5 =
      (Ideal.absNorm P.val : ℝ)^(-(5/2 : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hp0.le]
    congr 1
    norm_num
  simpa only [localMassTerm,he] using hh

def centralMass (d : Id × Id) : ℝ := idealPairWeight kernelCoeff (1/2) d

theorem central_ideal_mass (S : Finset PrimeIdeal)
    (hS : ∀ P ∈ S, Supported P.val) (D : Finset (Id × Id))
    (hD : ∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hs : ∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) :
    (∑ d ∈ D, centralMass d) ≤ Real.exp (11*rootMass (5/2)) := by
  calc
    _ ≤ ∏ P : S, ∑ ij ∈ D.image (fun d => encodePair S d P), localMassTerm kernelCoeff (1/2) P.val ij :=
      finite_ideal_mass_product kernelCoeff kernelCoeff_zero (1/2) D S hD hs
    _ ≤ ∏ P : S, (1+11*(Ideal.absNorm P.val.val : ℝ)^(-(5/2 : ℝ))) := by
      apply Finset.prod_le_prod₀
      · intro P _
        exact Finset.sum_nonneg (fun ij _ => localMassTerm_nonneg _ _ _ _)
      · intro P _
        exact local_central_bound P.val _
    _ = ∏ P ∈ primeValues S, (1+11*(Ideal.absNorm P : ℝ)^(-(5/2 : ℝ))) := by
      unfold primeValues
      rw [Finset.prod_image (by intro P hP Q hQ h; exact Subtype.val_injective h)]
      exact (Finset.prod_subtype (p := fun P => P ∈ S) S (by simp)
        (fun P : PrimeIdeal => 1+11*(Ideal.absNorm P.val : ℝ)^(-(5/2 : ℝ)))).symm
    _ ≤ _ := finite_euler_mass (5/2) 11 (by norm_num) (by norm_num) (primeValues S) (by
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
      exact hS Q hQ)

theorem central_ratio (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x^(-(1/2 : ℝ))*y^(-(1/2 : ℝ))*(y/x)^(1/6 : ℝ) =
      x^(-(2/3 : ℝ))*y^(-(1/3 : ℝ)) := by
  rw [Real.div_rpow hy.le hx.le,
    div_eq_mul_inv (y^(1/6 : ℝ)) (x^(1/6 : ℝ)),← Real.rpow_neg hx.le]
  calc
    _ = (x^(-(1/2 : ℝ))*x^(-(1/6 : ℝ)))*(y^(-(1/2 : ℝ))*y^(1/6 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hx,← Real.rpow_add hy]; norm_num

def reflectedMass (d : Id × Id) : ℝ :=
  centralMass d*(2+((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ))^(1/6 : ℝ))

theorem reflected_mass_split (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) :
    reflectedMass d = 2*centralMass d+KernelIdealMass.idealMass d := by
  have hx : (0 : ℝ) < Ideal.absNorm d.1 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hd.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hy : (0 : ℝ) < Ideal.absNorm d.2 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hd.2 (Ideal.absNorm_eq_zero_iff.mp h))
  have he := central_ratio _ _ hx hy
  unfold reflectedMass centralMass idealPairWeight KernelIdealMass.idealMass KernelIdeal.forwardIdeal normWeight
  nlinarith [mul_eq_mul_left_iff.mpr (Or.inl he : _ ∨ |(idealKernel kernelCoeff d.1 d.2 : ℝ)| = 0)]

/-- Uniform mass for the literal cost occurring in integrated_reference. -/
theorem reflected_ideal_mass (S : Finset PrimeIdeal)
    (hS : ∀ P ∈ S, Supported P.val) (D : Finset (Id × Id))
    (hD : ∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hs : ∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) :
    (∑ d ∈ D, reflectedMass d) ≤
      2*Real.exp (11*rootMass (5/2))+Real.exp (11*rootMass (5/3)) := by
  calc
    _ = 2*(∑ d ∈ D, centralMass d)+(∑ d ∈ D, KernelIdealMass.idealMass d) := by
      simp_rw [Finset.mul_sum,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun d hd => reflected_mass_split d (hD d hd))
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (central_ideal_mass S hS D hD hs) (by norm_num))
      (KernelIdealMass.forward_ideal_mass S hS D hD hs)

end
end Candidate.SilPrior.FourthPower.KernelReflectedMass
