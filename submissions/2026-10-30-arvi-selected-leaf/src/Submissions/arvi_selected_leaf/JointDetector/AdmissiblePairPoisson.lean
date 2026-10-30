/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.SelectedGauss
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.PrimePools

/-! Exact coprime pair Poisson for a finite admissible ideal family. The
unary Gauss coefficients are assigned to individual ideals before pairing. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge GaussGeneratorTransport FiniteGaussPhase
open MixedCrossSeparation MixedGaussConversion EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

local instance (F : Finset (Ideal O)) : DecidableEq (primePool F) := Classical.decEq _

theorem admissiblePoolMaximal (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) :
    ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal := by
  intro i
  rw [poolPrimary_span F hF i]
  infer_instance

/-- A row coefficient, independent of the second ideal and its support. -/
def admissibleUnaryGauss (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (j : ℕ) : ℂ :=
  let := admissiblePoolMaximal F hF
  unaryPairGauss (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_good F hF) (idealSupport F I) j

theorem admissibleUnaryGauss_norm (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) :
    ‖admissibleUnaryGauss F hF I j‖ = 1 := by
  let := admissiblePoolMaximal F hF
  exact unaryPairGauss_norm (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_odd F hF)
    (idealSupport F I) j hj0 hj6

theorem admissiblePoolProduct_span (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (I : Ideal O) (hIF : I ∈ F) :
    Ideal.span {∏ i ∈ idealSupport F I, poolPrimary F i} = I := by
  rw [span_finset_prod]
  simp_rw [poolPrimary_span F hF]
  exact idealSupport_product_eq F hIF (hF I hIF).2.1

def admissiblePairGauss (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I J : Ideal O) : ℂ :=
  let := admissiblePoolMaximal F hF
  selectedPairGauss (poolPrimary F) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) (idealSupport F I) (idealSupport F J)

theorem admissiblePairGauss_fixed_ray (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (I J : Ideal O) (hIF : I ∈ F) (hJF : J ∈ F)
    (hIJ : IsCoprime I J)
    (hmod : primaryGenerator I - primaryGenerator J ∈ (Ideal.span {(36 : O)} : Ideal O))
    (r : EisensteinEPrimaryPhase.Coord) (hr : residue (primaryGenerator J) = r) :
    admissiblePairGauss F hF I J = quadraticRayPair r r *
      admissibleUnaryGauss F hF I 1 * admissibleUnaryGauss F hF J 5 := by
  let := admissiblePoolMaximal F hF
  change selectedPairGauss (poolPrimary F) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) (idealSupport F I) (idealSupport F J) =
      quadraticRayPair r r *
        unaryPairGauss (poolPrimary F) (poolPrimary_ne_zero F hF)
          (poolPrimary_good F hF) (idealSupport F I) 1 *
        unaryPairGauss (poolPrimary F) (poolPrimary_ne_zero F hF)
          (poolPrimary_good F hF) (idealSupport F J) 5
  apply selectedPairGauss_fixed_ray (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_odd F hF)
  · intro i
    exact (primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2
  · exact idealSupport_disjoint_of_coprime F I J hIJ
  · rw [admissiblePoolProduct_span F hF I hIF]
    exact admissible_supported (hF I hIF)
  · rw [admissiblePoolProduct_span F hF J hJF]
    exact admissible_supported (hF J hJF)
  · simpa only [← primaryGenerator_eq_poolProduct F hF I hIF,
      ← primaryGenerator_eq_poolProduct F hF J hJF] using hmod
  · simpa only [← primaryGenerator_eq_poolProduct F hF J hJF] using hr

def admissiblePairConductor (F : Finset (Ideal O)) (I J : Ideal O) : O :=
  finitePrimeModulus (fun i : (idealSupport F I ∪ idealSupport F J : Finset (primePool F)) =>
    Ideal.span {poolPrimary F i.val})

theorem admissiblePairConductor_norm_sq (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (I J : Ideal O) (hIF : I ∈ F) (hJF : J ∈ F)
    (hIJ : IsCoprime I J) :
    ‖eisEmbedding (admissiblePairConductor F I J)‖ ^ 2 =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) := by
  unfold admissiblePairConductor
  rw [finitePrimeModulus_norm_sq, Finset.prod_coe_sort
    (idealSupport F I ∪ idealSupport F J) (fun i => Ideal.span {poolPrimary F i})]
  rw [Finset.prod_union (idealSupport_disjoint_of_coprime F I J hIJ)]
  simp_rw [poolPrimary_span F hF]
  rw [idealSupport_product_eq F hIF (hF I hIF).2.1,
    idealSupport_product_eq F hJF (hF J hJF).2.1, map_mul, Nat.cast_mul]

theorem admissiblePairConductor_norm (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (I J : Ideal O) (hIF : I ∈ F) (hJF : J ∈ F)
    (hIJ : IsCoprime I J) :
    ‖eisEmbedding (admissiblePairConductor F I J)‖ =
      Real.sqrt ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) := by
  rw [← admissiblePairConductor_norm_sq F hF I J hIF hJF hIJ, Real.sqrt_sq (norm_nonneg _)]

theorem admissibleIdealRow_zero (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (I : Ideal O) (hIF : I ∈ F) (hI1 : I ≠ 1) :
    idealRowHom 0 I = 0 := by
  have hS : (idealSupport F I).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hh := idealSupport_product_eq F hIF (hF I hIF).2.1
    rw [he, Finset.prod_empty] at hh
    exact hI1 hh.symm
  obtain ⟨P, hP⟩ := hS
  have hf := (mem_idealSupport_iff F I P).mp hP
  exact idealRowHom_zero_of_dvd 0
    (UniqueFactorizationMonoid.prime_of_normalized_factor P.val hf)
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hf) (Ideal.zero_mem _)

/-- The only coprime pair for which zero frequency can survive is the unit
pair; no principal term is subtracted from an upper bound. -/
theorem admissible_pair_zero_frequency (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (I J : Ideal O) (hIF : I ∈ F) (hJF : J ∈ F)
    (hIJ : I * J ≠ 1) : idealRowHom 0 I * star (idealRowHom 0 J) = 0 := by
  by_cases hI : I = 1
  · have hJ : J ≠ 1 := by simpa only [hI, one_mul] using hIJ
    rw [admissibleIdealRow_zero F hF J hJF hJ, star_zero, mul_zero]
  · rw [admissibleIdealRow_zero F hF I hIF hI, zero_mul]

/-- Element-source Poisson in the literal ideal-row orientation, with the
separated unary coefficients and the exact ideal conductor norm. -/
theorem admissible_pair_poisson (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (I J : Ideal O) (hIF : I ∈ F) (hJF : J ∈ F)
    (hIJ : IsCoprime I J)
    (hmod : primaryGenerator I - primaryGenerator J ∈ (Ideal.span {(36 : O)} : Ideal O))
    (r : EisensteinEPrimaryPhase.Coord) (hr : residue (primaryGenerator J) = r)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 < L) :
    (∑' z : O, (idealRowHom z I * star (idealRowHom z J)) *
      W (‖eisEmbedding z‖ ^ 2 / L)) =
    ((L : ℂ) / (Real.sqrt ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) : ℂ) *
      quadraticRayPair r r * admissibleUnaryGauss F hF I 1 * admissibleUnaryGauss F hF J 5) *
      ∑' h : O, star (idealRowHom h I * star (idealRowHom h J)) *
        paperRadialFourier W
          (L * ‖eisEmbedding h‖ ^ 2 / ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ))) := by
  let := admissiblePoolMaximal F hF
  let S := idealSupport F I
  let T := idealSupport F J
  let P := fun i : (S ∪ T : Finset (primePool F)) => Ideal.span {poolPrimary F i.val}
  have hcop := selectedPrimeCoprime (poolPrimary F) (poolPrimary_coprime F hF) (S ∪ T)
  have hrow (n : O) : finiteSexticRow P (fun i => poolPrimary_good F hF i.val)
      (fun i => if i.val ∈ T then 5 else 1) n = idealRowHom n I * star (idealRowHom n J) := by
    have hh := selectedPairRow_actual (poolPrimary F) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) S T (idealSupport_disjoint_of_coprime F I J hIJ) n
    rw [show S = idealSupport F I from rfl, show T = idealSupport F J from rfl,
      admissiblePoolProduct_span F hF I hIF, admissiblePoolProduct_span F hF J hJF] at hh
    exact hh
  have hh := canonical_radial_poisson_normalized P hcop
    (fun i => poolPrimary_good F hF i.val) (fun i => poolPrimary_odd F hF i.val)
    (fun i => if i.val ∈ T then 5 else 1) (fun i => by split_ifs <;> decide)
    (fun i => by split_ifs <;> decide) W L hL
  change (∑' z : O, finiteSexticRow P _ _ z * _) =
    ((L : ℂ) * admissiblePairGauss F hF I J /
      (‖eisEmbedding (admissiblePairConductor F I J)‖ : ℂ)) *
      ∑' h : O, star (finiteSexticRow P _ _ h) *
        paperRadialFourier W (L * ‖eisEmbedding h‖ ^ 2 /
          ‖eisEmbedding (admissiblePairConductor F I J)‖ ^ 2) at hh
  simp_rw [hrow] at hh
  rw [admissiblePairConductor_norm_sq F hF I J hIF hJF hIJ,
    admissiblePairConductor_norm F hF I J hIF hJF hIJ,
    admissiblePairGauss_fixed_ray F hF I J hIF hJF hIJ hmod r hr] at hh
  rw [hh]
  ring

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.admissibleUnaryGauss_norm
#print axioms Qrh.JointDetector.admissiblePairGauss_fixed_ray
#print axioms Qrh.JointDetector.admissible_pair_zero_frequency
#print axioms Qrh.JointDetector.admissible_pair_poisson
