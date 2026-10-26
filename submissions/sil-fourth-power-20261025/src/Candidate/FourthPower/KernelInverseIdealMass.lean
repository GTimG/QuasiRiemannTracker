/- Copyright (c) 2026 Sil. Apache-2.0.
Absolute central mass of the actual fifth-free inverse on ideal pairs.
The prime-norm threshold is derived from the original Supported predicate.
-/
import Candidate.FourthPower.KernelInverseMass
import Candidate.FourthPower.KernelIdealMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Eisenstein.UnitNormalization

set_option autoImplicit false
namespace Candidate.FourthPower.KernelInverseIdealMass
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open KernelFormal KernelIdeal KernelInverseMass KernelForwardMass SieveDescent
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem supported_prime_norm (P : PrimeIdeal) (hs : Supported P.val) :
    7 ≤ Ideal.absNorm P.val := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have hgood := hs.2 P.val ((Ideal.mem_normalizedFactors_iff hs.1).mpr ⟨inferInstance,le_rfl⟩)
  have hmod := CanonicalUnitEuler.good_prime_norm_mod_six P.val hgood.1 hgood.2
  have htwo := SmoothMobiusCorrection.prime_norm_two_le P
  omega

theorem central_radius {p : ℝ} (hp : 7 ≤ p) : p^(-(1/2 : ℝ)) ≤ 2/5 := by
  have hp0 : 0 < p := by linarith
  have hz : 0 ≤ p^(-(1/2 : ℝ)) := Real.rpow_nonneg hp0.le _
  have hsq : (p^(-(1/2 : ℝ)))^2 = p⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hp0.le]
    norm_num [Real.rpow_neg_one]
  have hinv : p⁻¹ ≤ (7 : ℝ)⁻¹ := (inv_le_inv₀ hp0 (by norm_num)).mpr hp
  nlinarith

theorem local_central_mass (P : PrimeIdeal) (hs : Supported P.val) (T : Finset (ℕ × ℕ)) :
    (∑ ij ∈ T, localMass ((Ideal.absNorm P.val : ℝ)^(-(1/2 : ℝ))) ij) ≤
      1+400*(Ideal.absNorm P.val : ℝ)^(-(3/2 : ℝ)) := by
  have hp : (7 : ℝ) ≤ Ideal.absNorm P.val := by exact_mod_cast supported_prime_norm P hs
  have hp0 : (0 : ℝ) < Ideal.absNorm P.val := by linarith
  have hh := localMass_finite T (Real.rpow_nonneg hp0.le (-(1/2 : ℝ))) (central_radius hp)
  have he : ((Ideal.absNorm P.val : ℝ)^(-(1/2 : ℝ)))^3 =
      (Ideal.absNorm P.val : ℝ)^(-(3/2 : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hp0.le]
    congr 1
    norm_num
  simpa only [he] using hh

def idealMass (d : Id × Id) : ℝ :=
  |(inverseIdeal d.1 d.2 : ℝ)| * normWeight (1/2) d.1 * normWeight (1/2) d.2

theorem idealMass_nonneg (d : Id × Id) : 0 ≤ idealMass d := by
  unfold idealMass normWeight
  positivity

theorem ideal_mass_product (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (S : Finset PrimeIdeal) (hs : pairSupport d.1 d.2 ⊆ primeValues S) :
    idealMass d = ∏ P : S,
      localMass ((Ideal.absNorm P.val.val : ℝ)^(-(1/2 : ℝ))) (encodePair S d P) := by
  unfold idealMass inverseIdeal
  rw [kernel_eq_prime_prod reciprocalCoeff reciprocalCoeff_zero hd.1 hd.2 S hs,
    KernelIdealMass.normWeight_prime_product (1/2) hd.1 S
      (Finset.Subset.trans Finset.subset_union_left hs),
    KernelIdealMass.normWeight_prime_product (1/2) hd.2 S
      (Finset.Subset.trans Finset.subset_union_right hs)]
  push_cast
  rw [Finset.abs_prod,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [localMass,encodePair,localExponent,pow_add,mul_assoc]

theorem configuration_mass (S : Finset PrimeIdeal) (hS : ∀ P ∈ S, Supported P.val)
    (T : S → Finset (ℕ × ℕ)) :
    (∑ a ∈ Fintype.piFinset T, ∏ P : S,
      localMass ((Ideal.absNorm P.val.val : ℝ)^(-(1/2 : ℝ))) (a P)) ≤
      Real.exp (400*rootMass (3/2)) := by
  rw [← Finset.prod_univ_sum T (fun P : S =>
    localMass ((Ideal.absNorm P.val.val : ℝ)^(-(1/2 : ℝ))))]
  calc
    _ ≤ ∏ P : S, (1+400*(Ideal.absNorm P.val.val : ℝ)^(-(3/2 : ℝ))) := by
      apply Finset.prod_le_prod₀
      · intro P _
        exact Finset.sum_nonneg (fun ij _ => localMass_nonneg (by positivity) ij)
      · intro P _
        exact local_central_mass P.val (hS P.val P.property) (T P)
    _ = ∏ P ∈ primeValues S, (1+400*(Ideal.absNorm P : ℝ)^(-(3/2 : ℝ))) := by
      unfold primeValues
      rw [Finset.prod_image (by intro P hP Q hQ h; exact Subtype.val_injective h)]
      exact (Finset.prod_subtype (p := fun P => P ∈ S) S (by simp)
        (fun P : PrimeIdeal => 1+400*(Ideal.absNorm P.val : ℝ)^(-(3/2 : ℝ)))).symm
    _ ≤ _ := finite_euler_mass (3/2) 400 (by norm_num) (by norm_num) (primeValues S) (by
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
      exact hS Q hQ)

/-- Uniform over every finite set of ideal pairs, with no inverse-mass assumption. -/
theorem inverse_ideal_mass (S : Finset PrimeIdeal) (hS : ∀ P ∈ S, Supported P.val)
    (D : Finset (Id × Id)) (hD : ∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hs : ∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) :
    (∑ d ∈ D, idealMass d) ≤ Real.exp (400*rootMass (3/2)) := by
  let enc : D → S → ℕ × ℕ := fun d => encodePair S d.val
  let T : S → Finset (ℕ × ℕ) := fun P => Finset.univ.image (fun d : D => enc d P)
  have hinj : Function.Injective enc := by
    intro d e he
    apply Subtype.ext
    exact encodePair_injective (hD d.val d.property) (hD e.val e.property)
      (hs d.val d.property) (hs e.val e.property) he
  have hsubset : Finset.univ.image enc ⊆ Fintype.piFinset T := by
    intro a ha
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    exact Fintype.mem_piFinset.mpr (fun P => Finset.mem_image.mpr ⟨d,Finset.mem_univ d,rfl⟩)
  rw [← Finset.sum_coe_sort D idealMass]
  calc
    _ = ∑ a ∈ Finset.univ.image enc, ∏ P : S,
        localMass ((Ideal.absNorm P.val.val : ℝ)^(-(1/2 : ℝ))) (a P) := by
      rw [Finset.sum_image (fun d _ e _ h => hinj h)]
      exact Finset.sum_congr rfl (fun d _ => ideal_mass_product d.val (hD d.val d.property) S
        (hs d.val d.property))
    _ ≤ ∑ a ∈ Fintype.piFinset T, ∏ P : S,
        localMass ((Ideal.absNorm P.val.val : ℝ)^(-(1/2 : ℝ))) (a P) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun a _ _ => Finset.prod_nonneg (fun P _ => localMass_nonneg (by positivity) _))
    _ ≤ _ := configuration_mass S hS T

end
end Candidate.FourthPower.KernelInverseIdealMass
