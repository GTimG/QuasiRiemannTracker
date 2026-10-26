/- Copyright (c) 2026 Sil. Apache-2.0.
Actual ideal kernels, with the anisotropic weight required by reflection.
Finite nonzero ideal terms inject into the already checked monomial configurations.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.KernelIdeal
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.KernelCoefficients

set_option autoImplicit false
namespace Candidate.FourthPower.KernelIdealMass
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open KernelFormal KernelIdeal KernelCoefficients KernelForwardMass SieveDescent
local notation "Id" => Ideal ActualEisensteinCubic.O

def idealMass (d : Id × Id) : ℝ :=
  |(forwardIdeal d.1 d.2 : ℝ)| * normWeight (2/3) d.1 * normWeight (1/3) d.2

theorem idealMass_nonneg (d : Id × Id) : 0 ≤ idealMass d := by
  unfold idealMass normWeight
  positivity

theorem normWeight_prime_product (σ : ℝ) {I : Id} (hI : I ≠ 0)
    (S : Finset PrimeIdeal) (hs : primeSupport I ⊆ primeValues S) :
    normWeight σ I = ∏ P : S, ((Ideal.absNorm P.val.val : ℝ)^(-σ))^(valuation I P.val.val) := by
  rw [normWeight_eq_prod hI (primeValues S) hs σ]
  unfold primeValues
  rw [Finset.prod_image (by intro P hP Q hQ h; exact Subtype.val_injective h)]
  exact Finset.prod_subtype (p := fun P => P ∈ S) S (by simp) _

theorem ideal_mass_product (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (S : Finset PrimeIdeal) (hs : pairSupport d.1 d.2 ⊆ primeValues S) :
    idealMass d = ∏ P : S,
      |(kernelCoeff (exponent (valuation d.1 P.val.val) (valuation d.2 P.val.val)) : ℝ)| *
      ((Ideal.absNorm P.val.val : ℝ)^(-(2/3 : ℝ)))^(valuation d.1 P.val.val) *
      ((Ideal.absNorm P.val.val : ℝ)^(-(1/3 : ℝ)))^(valuation d.2 P.val.val) := by
  unfold idealMass forwardIdeal
  rw [kernel_eq_prime_prod kernelCoeff kernelCoeff_zero hd.1 hd.2 S hs,
    normWeight_prime_product (2/3) hd.1 S (Finset.Subset.trans Finset.subset_union_left hs),
    normWeight_prime_product (1/3) hd.2 S (Finset.Subset.trans Finset.subset_union_right hs)]
  push_cast
  rw [Finset.abs_prod,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  rfl

theorem local_coefficient_mass (p : ℝ) (hp : 0 < p) (i : Fin 12) :
    |(kernelCoeff (exponent (ordinaryExponent i).1 (ordinaryExponent i).2) : ℝ)| *
      (p^(-(2/3 : ℝ)))^(ordinaryExponent i).1*(p^(-(1/3 : ℝ)))^(ordinaryExponent i).2 =
      ordinaryWeight p i := by
  rw [ordinary_coefficient_at_index]
  have he : (p^(-(2/3 : ℝ)))^(ordinaryExponent i).1 *
      (p^(-(1/3 : ℝ)))^(ordinaryExponent i).2 =
      p^(-((2*(ordinaryExponent i).1+(ordinaryExponent i).2 : ℝ)/3)) := by
    simp only [← Real.rpow_natCast,← Real.rpow_mul hp.le,← Real.rpow_add hp]
    congr 1
    ring
  rw [mul_assoc,he]
  rfl

/-- The full finite mass of the actual ideal kernel is bounded uniformly in
both the ideal set and its prime pool. No coefficient-mass hypothesis is assumed. -/
theorem forward_ideal_mass (S : Finset PrimeIdeal)
    (hS : ∀ P ∈ S, Supported P.val) (D : Finset (Id × Id))
    (hD : ∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hs : ∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) :
    (∑ d ∈ D, idealMass d) ≤ Real.exp (11*rootMass (5/3)) := by
  let A := D.filter (fun d => forwardIdeal d.1 d.2 ≠ 0)
  have hAD (d : A) : d.val ∈ D := (Finset.mem_filter.mp d.property).1
  have hc (d : A) (P : S) :
      kernelCoeff (exponent (valuation d.val.1 P.val.val) (valuation d.val.2 P.val.val)) ≠ 0 := by
    have hn := (Finset.mem_filter.mp d.property).2
    rw [forwardIdeal,kernel_eq_prime_prod kernelCoeff kernelCoeff_zero
      (hD d.val (hAD d)).1 (hD d.val (hAD d)).2 S (hs d.val (hAD d))] at hn
    exact Finset.prod_ne_zero_iff.mp hn P (Finset.mem_univ P)
  choose enc henc using (fun (d : A) (P : S) =>
    ordinary_coefficient_nonzero _ _ (hc d P))
  have hinj : Function.Injective enc := by
    intro d e he
    apply Subtype.ext
    apply encodePair_injective (hD d.val (hAD d)) (hD e.val (hAD e))
      (hs d.val (hAD d)) (hs e.val (hAD e))
    funext P
    exact (henc d P).symm.trans ((congrArg ordinaryExponent (congrFun he P)).trans (henc e P))
  have hmass (d : A) : idealMass d.val =
      ∏ P : S, ordinaryWeight (Ideal.absNorm P.val.val : ℝ) (enc d P) := by
    rw [ideal_mass_product d.val (hD d.val (hAD d)) S (hs d.val (hAD d))]
    apply Finset.prod_congr rfl
    intro P hP
    have hi := congrArg Prod.fst (henc d P)
    have hj := congrArg Prod.snd (henc d P)
    dsimp only at hi hj
    rw [← hi,← hj]
    exact local_coefficient_mass _
      (zero_lt_one.trans_le (CenteredExceptionalCount.norm_one_le (hS P.val P.property).1)) _
  have hfilter : (∑ d ∈ D, idealMass d) = ∑ d : A, idealMass d.val := by
    rw [Finset.sum_coe_sort A idealMass]
    dsimp only [A]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hn : forwardIdeal d.1 d.2 = 0
    · simp [idealMass,hn]
    · simp [hn]
  rw [hfilter]
  calc
    _ = ∑ a ∈ Finset.univ.image enc, ∏ P : S,
        ordinaryWeight (Ideal.absNorm P.val.val : ℝ) (a P) := by
      rw [Finset.sum_image (fun d _ e _ h => hinj h)]
      exact Finset.sum_congr rfl (fun d _ => hmass d)
    _ ≤ ∑ a : S → Fin 12, ∏ P : S, ordinaryWeight (Ideal.absNorm P.val.val : ℝ) (a P) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun a _ _ => Finset.prod_nonneg (fun P _ => ordinaryWeight_nonneg _ (Nat.cast_nonneg _) _))
    _ = ∏ P : S, ∑ i : Fin 12, ordinaryWeight (Ideal.absNorm P.val.val : ℝ) i :=
      (Fintype.prod_sum (fun P : S => fun i : Fin 12 =>
        ordinaryWeight (Ideal.absNorm P.val.val : ℝ) i)).symm
    _ = ∏ P ∈ primeValues S, ∑ i : Fin 12, ordinaryWeight (Ideal.absNorm P : ℝ) i := by
      unfold primeValues
      rw [Finset.prod_image (by intro P hP Q hQ h; exact Subtype.val_injective h)]
      exact (Finset.prod_subtype (p := fun P => P ∈ S) S (by simp)
        (fun P : PrimeIdeal => ∑ i : Fin 12, ordinaryWeight (Ideal.absNorm P.val : ℝ) i)).symm
    _ ≤ _ := ordinary_global_mass (primeValues S) (by
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
      exact hS Q hQ)

end
end Candidate.FourthPower.KernelIdealMass
