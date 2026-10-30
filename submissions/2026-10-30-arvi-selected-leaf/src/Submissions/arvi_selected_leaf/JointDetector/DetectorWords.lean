/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.IdealMultiplicity
import Submissions.arvi_selected_leaf.JointDetector.RefinedPrice
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialRawDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorFiberSpikes
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorFiberEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCount

/-!
# The three actual detector words

The coefficient adapter below is for the existing OAI dyadic detector, including
its Möbius factor and normalization. Products are merged into the full ordinary
ideal family. In particular, squaring a polynomial does not square its row
character: the feature at the product ideal is still `idealRowHom z`.

This file proves finite algebra, coefficient masses, responses, and finite
energy-to-cardinality estimates. It does not assert an analytic estimate for
`selectedNorm`, or an asymptotic zero count.
-/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ComplexConjugate
open OAI OAI.SevenEighths
open CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeRowClosure
open HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
local notation "O" => ActualEisensteinCubic.O

/-- The common source coefficient of the actual normalized dyadic detector.
The inverse factor is the ordinary ideal Möbius function, with its signs. -/
def detectorCoefficient (base : Ideal O → ℂ) (inverse : Bool)
    (W : ℝ → ℂ) (D σ freq : ℝ) (I : Ideal O) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ)) *
    ((if inverse then (UniqueFactorizationMonoid.moebius I : ℂ) else 1) * base I) *
    W ((I.absNorm : ℝ)/D) *
    (((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq)

/-- An ordinary polynomial with the original sextic row feature. -/
def ordinaryPolynomial (sources : Finset (Ideal O))
    (c : sources → ℂ) (z : O) : ℂ :=
  ∑ I : sources, c I * idealRowHom z I.val

/-- The literal detector polynomial, without deleting natural zeros, is an
ordinary polynomial with one common coefficient vector. -/
theorem detector_polynomial_eq (χ : Character) (base : Ideal O → ℂ) (z : O)
    (hrow : ∀ I : Ideal O, idealCoeff χ I = base I * idealRowHom z I)
    (inverse : Bool) (W : ℝ → ℂ) (D σ freq : ℝ) (sources : Finset (Ideal O))
    (hcover : ∀ I : Ideal O, I ≠ 0 → W ((I.absNorm : ℝ)/D) ≠ 0 → I ∈ sources) :
    polynomial χ inverse W D σ freq =
      ordinaryPolynomial sources
        (fun I => detectorCoefficient base inverse W D σ freq I.val) z := by
  rw [polynomial_eq_finite χ inverse W D σ freq sources hcover]
  rw [ordinaryPolynomial, Finset.sum_coe_sort sources
    (fun I => detectorCoefficient base inverse W D σ freq I * idealRowHom z I)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  cases inverse <;> simp only [HeckeDyadic.coefficient, Bool.false_eq_true,
    ite_false, ite_true, hrow, detectorCoefficient] <;> ring

/-- The actual fixed dictionary supplies precisely the common base needed by
`detector_polynomial_eq`. Here `m,f` are fixed dictionary data. Applying the
detector to free core presentations avoids any moving sixth-root conductor. -/
theorem detector_polynomial_eq_fixedBase (η χ : Character) (m f z : O)
    (hrow : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (inverse : Bool) (W : ℝ → ℂ) (D σ freq : ℝ) (sources : Finset (Ideal O))
    (hcover : ∀ I : Ideal O, I ≠ 0 → W ((I.absNorm : ℝ)/D) ≠ 0 → I ∈ sources) :
    polynomial χ inverse W D σ freq = ordinaryPolynomial sources
      (fun I => detectorCoefficient (InverseInitialRawDictionary.fixedBase η m f)
        inverse W D σ freq I.val) z :=
  detector_polynomial_eq χ _ z
    (InverseInitialRawDictionary.fixedBase_row η χ m f z hrow)
    inverse W D σ freq sources hcover

theorem detector_fixedBase_norm_le_one (η : Character) (m f : O) (I : Ideal O) :
    ‖InverseInitialRawDictionary.fixedBase η m f I‖ ≤ 1 := by
  change ‖idealCoeff η I * idealRowHom (m^6*f^4) I‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_mul (idealCoeff_norm_le_one η I) (idealRowHom_norm _ _)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

private theorem annular_power_bound {x σ : ℝ} (hx : (1/4 : ℝ) ≤ x)
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1) : x ^ (-σ) ≤ 4 := by
  have hxpos : 0 < x := by linarith
  by_cases hx1 : 1 ≤ x
  · have h : x ^ (-σ) ≤ 1 := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le hx1 (show -σ ≤ 0 by linarith [hσ.1])
    exact h.trans (by norm_num)
  · have h := Real.rpow_le_rpow_of_exponent_ge hxpos (le_of_not_ge hx1)
      (show (-1 : ℝ) ≤ -σ by linarith [hσ.2])
    rw [Real.rpow_neg_one] at h
    have hxinv : x⁻¹ ≤ 4 := by
      rw [← one_div]
      exact (div_le_iff₀ hxpos).2 (by linarith)
    exact h.trans hxinv

/-- The actual normalized detector coefficients have bounded square mass on
an annular source family, uniformly in the common real part and frequency. -/
theorem detectorCoefficient_norm_sq_le (base : Ideal O → ℂ)
    (hbase : ∀ I, ‖base I‖ ≤ 1) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq L : ℝ) (hD : 0 < D) (_hL : 0 ≤ L)
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hsupport : Function.support W ⊆ Set.Icc (1/4 : ℝ) (9/4))
    (hW : ∀ x, ‖W x‖ ≤ L) (I : Ideal O) :
    ‖detectorCoefficient base inverse W D σ freq I‖ ^ 2 ≤ 16*L^2/D := by
  by_cases hz : W ((I.absNorm : ℝ)/D) = 0
  · simp only [detectorCoefficient, hz, mul_zero, zero_mul, norm_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  have hx := hsupport (show (I.absNorm : ℝ)/D ∈ Function.support W from hz)
  have hxpos : 0 < (I.absNorm : ℝ)/D := by linarith [hx.1]
  have hp : ‖(((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq)‖ ≤ 4 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.neg_re, HeckeDyadic.shift_re]
    exact annular_power_bound hx.1 hσ
  have hm : ‖(if inverse then (UniqueFactorizationMonoid.moebius I : ℂ) else 1) * base I‖ ≤ 1 := by
    rw [norm_mul]
    have hμ : ‖(if inverse then (UniqueFactorizationMonoid.moebius I : ℂ) else 1)‖ ≤ 1 := by
      cases inverse
      · simp
      · exact CubicEisenstein.norm_ideal_moebius_le_one I
    exact (mul_le_mul hμ (hbase I) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hnormD : ‖(D : ℂ)^(-(1/2 : ℂ))‖ ^ 2 = D⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]
    have hre : (-(1/2 : ℂ)).re = -(1/2 : ℝ) := by norm_num
    rw [hre]
    rw [← Real.rpow_two, ← Real.rpow_mul hD.le]
    norm_num only [neg_div, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_neg_one]
  calc
    _ = ‖(D : ℂ)^(-(1/2 : ℂ))‖ ^ 2 *
        ‖(if inverse then (UniqueFactorizationMonoid.moebius I : ℂ) else 1) * base I‖ ^ 2 *
        ‖W ((I.absNorm : ℝ)/D)‖ ^ 2 *
        ‖(((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq)‖ ^ 2 := by
      simp only [detectorCoefficient, norm_mul, mul_pow]
    _ ≤ D⁻¹ * 1 * L^2 * 16 := by
      rw [hnormD]
      gcongr
      · nlinarith [norm_nonneg ((if inverse then
          (UniqueFactorizationMonoid.moebius I : ℂ) else 1) * base I)]
      · exact hW _
      · nlinarith [norm_nonneg
          ((((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq))]
    _ = _ := by ring

/-- An ordinary ideal family of scale `D` has bounded normalized coefficient
mass. This estimate does not require the ideals to be squarefree. -/
theorem detectorCoefficient_mass (S : Finset (Ideal O)) (base : Ideal O → ℂ)
    (hbase : ∀ I, ‖base I‖ ≤ 1) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq L : ℝ) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hsupport : Function.support W ⊆ Set.Icc (1/4 : ℝ) (9/4))
    (hW : ∀ x, ‖W x‖ ≤ L)
    (hnonzero : ∀ I ∈ S, I ≠ ⊥) (hnorm : ∀ I ∈ S, (I.absNorm : ℝ) ≤ (9/4)*D) :
    ∑ I : S, ‖detectorCoefficient base inverse W D σ freq I.val‖ ^ 2 ≤ 4608*L^2 := by
  have hDp : 0 < D := by linarith
  have hc := DescentFiberCost.finite_ideal_count_real S ((9/4)*D) (by linarith)
    hnonzero hnorm
  calc
    _ ≤ ∑ _I : S, 16*L^2/D := Finset.sum_le_sum fun I _ =>
      detectorCoefficient_norm_sq_le base hbase inverse W D σ freq L hDp hL hσ hsupport hW I.val
    _ = (S.card : ℝ) * (16*L^2/D) := by simp
    _ ≤ (128*((9/4)*D)) * (16*L^2/D) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by field_simp; ring

/-- Merging retains every summand in every fiber. -/
def mergedCoefficient {P T : Type*} [Fintype P] [DecidableEq T]
    (merge : P → T) (c : P → ℂ) (t : T) : ℂ :=
  ∑ p ∈ Finset.univ.filter (fun p => merge p = t), c p

theorem mergedCoefficient_sum {P T : Type*} [Fintype P] [Fintype T] [DecidableEq T]
    (merge : P → T) (c : P → ℂ) (F : T → ℂ) :
    (∑ t, mergedCoefficient merge c t * F t) = ∑ p, c p * F (merge p) := by
  simp only [mergedCoefficient, Finset.sum_mul]
  have h := Finset.sum_fiberwise (Finset.univ : Finset P) merge
    (fun p => c p * F (merge p))
  rw [← h]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem mergedCoefficient_mass {P T : Type*} [Fintype P] [Fintype T] [DecidableEq T]
    (merge : P → T) (c : P → ℂ) (D : ℝ)
    (hfiber : ∀ t, ((Finset.univ.filter fun p => merge p = t).card : ℝ) ≤ D) :
    ∑ t, ‖mergedCoefficient merge c t‖ ^ 2 ≤ D * ∑ p, ‖c p‖ ^ 2 := by
  have hlocal (t : T) : ‖mergedCoefficient merge c t‖ ^ 2 ≤
      D * ∑ p ∈ Finset.univ.filter (fun p => merge p = t), ‖c p‖ ^ 2 := by
    let fiber := Finset.univ.filter fun p => merge p = t
    have hc := coefficient_cauchy (fun (_ : fiber) => (1 : ℂ)) (fun p => c p.val)
    have hc' : ‖mergedCoefficient merge c t‖ ^ 2 ≤
        (fiber.card : ℝ) * ∑ p ∈ fiber, ‖c p‖ ^ 2 := by
      simpa only [one_mul, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul,
        mul_one, Finset.card_univ, Fintype.card_coe,
        Finset.sum_coe_sort fiber (fun p => c p),
        Finset.sum_coe_sort fiber (fun p => ‖c p‖ ^ 2), mergedCoefficient] using hc
    exact hc'.trans (mul_le_mul_of_nonneg_right (hfiber t)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  calc
    _ ≤ ∑ t, D * ∑ p ∈ Finset.univ.filter (fun p => merge p = t), ‖c p‖ ^ 2 :=
      Finset.sum_le_sum fun t _ => hlocal t
    _ = D * ∑ t, ∑ p ∈ Finset.univ.filter (fun p => merge p = t), ‖c p‖ ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by
      congr 1
      exact Finset.sum_fiberwise Finset.univ merge _

/-- Full ordinary ideal convolution. Units and all shared-prime products stay. -/
def idealConvolution (S T : Finset (Ideal O)) (a : S → ℂ) (b : T → ℂ) :
    idealProductSources S T → ℂ :=
  mergedCoefficient
    (idealProductMerge S T (idealProductSources S T)
      (fun _ hI _ hJ => mul_mem_idealProductSources hI hJ))
    (fun p => a p.1 * b p.2)

theorem ordinaryPolynomial_mul (S T : Finset (Ideal O))
    (a : S → ℂ) (b : T → ℂ) (z : O) :
    ordinaryPolynomial S a z * ordinaryPolynomial T b z =
      ordinaryPolynomial (idealProductSources S T) (idealConvolution S T a b) z := by
  simp only [ordinaryPolynomial, idealConvolution]
  rw [mergedCoefficient_sum]
  simp only [idealProductMerge_val, map_mul, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  ring

theorem idealConvolution_mass (S T : Finset (Ideal O))
    (a : S → ℂ) (b : T → ℂ) (D : ℝ)
    (hfiber : ∀ I ∈ idealProductSources S T,
      (((S ×ˢ T).filter fun p => p.1 * p.2 = I).card : ℝ) ≤ D) :
    ∑ I, ‖idealConvolution S T a b I‖ ^ 2 ≤
      D * (∑ I, ‖a I‖ ^ 2) * ∑ J, ‖b J‖ ^ 2 := by
  have h := mergedCoefficient_mass
    (idealProductMerge S T (idealProductSources S T)
      (fun _ hI _ hJ => mul_mem_idealProductSources hI hJ))
    (fun p => a p.1 * b p.2) D (fun I => by
      rw [idealProductMerge_fiber_card]
      exact hfiber I.val I.property)
  simpa only [idealConvolution, norm_mul, mul_pow, Fintype.sum_prod_type,
    ← Finset.mul_sum, ← Finset.sum_mul, mul_assoc] using h

theorem idealConvolution_mass_small_power (S T : Finset (Ideal O))
    (a : S → ℂ) (b : T → ℂ) (ε X : ℝ) (hε : 0 < ε)
    (hnonzero : ∀ I ∈ idealProductSources S T, I ≠ ⊥)
    (hnorm : ∀ I ∈ idealProductSources S T, (I.absNorm : ℝ) ≤ X) :
    ∑ I, ‖idealConvolution S T a b I‖ ^ 2 ≤
      idealDivisorConstant ε hε * X ^ ε * (∑ I, ‖a I‖ ^ 2) * ∑ J, ‖b J‖ ^ 2 :=
  idealConvolution_mass S T a b _ (fun I hI =>
    idealProduct_fiber_small_power S T I (hnonzero I hI) ε hε X (hnorm I hI))

/-- Primal selected energy is bounded by the very same exact operator norm.
The conjugation here is of the whole source vector and whole output. -/
theorem ordinaryPolynomial_energy (rows : Finset O) (S : Finset (Ideal O)) (c : S → ℂ) :
    ∑ z : rows, ‖ordinaryPolynomial S c z.val‖ ^ 2 ≤
      selectedNorm rows S * ∑ I, ‖c I‖ ^ 2 := by
  have h := FiniteSieveOperator.energy_bound
    (selectedMatrix rows S).conjTranspose (fun I => star (c I))
  rw [FiniteSieveOperator.operator_conjTranspose_norm] at h
  have heq (z : rows) :
      (∑ I : S, (selectedMatrix rows S).conjTranspose z I * star (c I)) =
        star (ordinaryPolynomial S c z.val) := by
    simp only [Matrix.conjTranspose_apply, selectedMatrix, ordinaryPolynomial,
      star_sum, star_mul]
  simpa only [heq, norm_star, selectedNorm] using h

theorem ordinaryPolynomial_product_energy (rows : Finset O) (S T : Finset (Ideal O))
    (a : S → ℂ) (b : T → ℂ) (ε X : ℝ) (hε : 0 < ε)
    (hnonzero : ∀ I ∈ idealProductSources S T, I ≠ ⊥)
    (hnorm : ∀ I ∈ idealProductSources S T, (I.absNorm : ℝ) ≤ X) :
    ∑ z : rows, ‖ordinaryPolynomial S a z.val * ordinaryPolynomial T b z.val‖ ^ 2 ≤
      selectedNorm rows (idealProductSources S T) *
        (idealDivisorConstant ε hε * X ^ ε * (∑ I, ‖a I‖ ^ 2) * ∑ J, ‖b J‖ ^ 2) := by
  simp_rw [ordinaryPolynomial_mul]
  exact (ordinaryPolynomial_energy rows _ _).trans
    (mul_le_mul_of_nonneg_left (idealConvolution_mass_small_power S T a b ε X hε hnonzero hnorm)
      (sq_nonneg _))

/-- The raw inverse (or plain) moment from the selected norm and the actual
normalized coefficient mass. The common fixed dictionary twist stays in `base`. -/
theorem detector_raw_energy (rows : Finset O) (χ : O → Character) (base : Ideal O → ℂ)
    (hrow : ∀ z ∈ rows, ∀ I : Ideal O, idealCoeff (χ z) I = base I * idealRowHom z I)
    (hbase : ∀ I, ‖base I‖ ≤ 1) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq L : ℝ) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hsupport : Function.support W ⊆ Set.Icc (1/4 : ℝ) (9/4))
    (hW : ∀ x, ‖W x‖ ≤ L) (S : Finset (Ideal O))
    (hcover : ∀ I : Ideal O, I ≠ 0 → W ((I.absNorm : ℝ)/D) ≠ 0 → I ∈ S)
    (hnonzero : ∀ I ∈ S, I ≠ ⊥) (hnorm : ∀ I ∈ S, (I.absNorm : ℝ) ≤ (9/4)*D) :
    ∑ z ∈ rows, ‖polynomial (χ z) inverse W D σ freq‖ ^ 2 ≤
      selectedNorm rows S * (4608*L^2) := by
  let coeff : S → ℂ := fun I => detectorCoefficient base inverse W D σ freq I.val
  have heq : (∑ z ∈ rows, ‖polynomial (χ z) inverse W D σ freq‖ ^ 2) =
      ∑ z : rows, ‖ordinaryPolynomial S coeff z.val‖ ^ 2 := by
    rw [Finset.sum_coe_sort rows (fun z => ‖ordinaryPolynomial S coeff z‖ ^ 2)]
    exact Finset.sum_congr rfl fun z hz => congrArg (fun v : ℂ => ‖v‖ ^ 2)
      (detector_polynomial_eq (χ z) base z (hrow z hz) inverse W D σ freq S hcover)
  rw [heq]
  exact (ordinaryPolynomial_energy rows S coeff).trans (mul_le_mul_of_nonneg_left
    (detectorCoefficient_mass S base hbase inverse W D σ freq L hD hL hσ hsupport hW hnonzero hnorm)
    (sq_nonneg _))

/-- The actual raw mixed moment. For the squared plain moment take both
inverse flags false and take identical profiles and source sets. No new
analytic hypothesis beyond the selected norm is hidden in the product. -/
theorem detector_raw_product_energy (rows : Finset O) (χ : O → Character)
    (base : Ideal O → ℂ)
    (hrow : ∀ z ∈ rows, ∀ I : Ideal O, idealCoeff (χ z) I = base I * idealRowHom z I)
    (hbase : ∀ I, ‖base I‖ ≤ 1) (invM invS : Bool) (WM WS : ℝ → ℂ)
    (D N σ freq LM LS ε X : ℝ) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (hLM : 0 ≤ LM) (hLS : 0 ≤ LS) (hε : 0 < ε) (hX : 0 ≤ X)
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hsM : Function.support WM ⊆ Set.Icc (1/4 : ℝ) (9/4))
    (hsS : Function.support WS ⊆ Set.Icc (1/4 : ℝ) (9/4))
    (hWM : ∀ x, ‖WM x‖ ≤ LM) (hWS : ∀ x, ‖WS x‖ ≤ LS)
    (SM SS : Finset (Ideal O))
    (hcM : ∀ I : Ideal O, I ≠ 0 → WM ((I.absNorm : ℝ)/D) ≠ 0 → I ∈ SM)
    (hcS : ∀ I : Ideal O, I ≠ 0 → WS ((I.absNorm : ℝ)/N) ≠ 0 → I ∈ SS)
    (hM0 : ∀ I ∈ SM, I ≠ ⊥) (hS0 : ∀ I ∈ SS, I ≠ ⊥)
    (hnM : ∀ I ∈ SM, (I.absNorm : ℝ) ≤ (9/4)*D)
    (hnS : ∀ I ∈ SS, (I.absNorm : ℝ) ≤ (9/4)*N)
    (hp0 : ∀ I ∈ idealProductSources SM SS, I ≠ ⊥)
    (hnp : ∀ I ∈ idealProductSources SM SS, (I.absNorm : ℝ) ≤ X) :
    ∑ z ∈ rows, ‖polynomial (χ z) invM WM D σ freq *
      polynomial (χ z) invS WS N σ freq‖ ^ 2 ≤
      selectedNorm rows (idealProductSources SM SS) *
        (idealDivisorConstant ε hε * X ^ ε * (4608*LM^2) * (4608*LS^2)) := by
  let cM : SM → ℂ := fun I => detectorCoefficient base invM WM D σ freq I.val
  let cS : SS → ℂ := fun I => detectorCoefficient base invS WS N σ freq I.val
  have hMmass := detectorCoefficient_mass SM base hbase invM WM D σ freq LM
    hD hLM hσ hsM hWM hM0 hnM
  have hSmass := detectorCoefficient_mass SS base hbase invS WS N σ freq LS
    hN hLS hσ hsS hWS hS0 hnS
  have heq : (∑ z ∈ rows, ‖polynomial (χ z) invM WM D σ freq *
      polynomial (χ z) invS WS N σ freq‖ ^ 2) =
      ∑ z : rows, ‖ordinaryPolynomial SM cM z.val * ordinaryPolynomial SS cS z.val‖ ^ 2 := by
    rw [Finset.sum_coe_sort rows
      (fun z => ‖ordinaryPolynomial SM cM z * ordinaryPolynomial SS cS z‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro z hz
    rw [detector_polynomial_eq (χ z) base z (hrow z hz) invM WM D σ freq SM hcM,
      detector_polynomial_eq (χ z) base z (hrow z hz) invS WS N σ freq SS hcS]
  rw [heq]
  refine (ordinaryPolynomial_product_energy rows SM SS cM cS ε X hε hp0 hnp).trans ?_
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hdiv : 0 ≤ idealDivisorConstant ε hε * X^ε :=
    mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg hX _)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hMmass hdiv) hSmass
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (mul_nonneg hdiv (by positivity))

/-- The count step uses a genuine lower response and a coefficient mass,
instead of postulating the desired count. -/
theorem ordinaryPolynomial_count (rows : Finset O) (S : Finset (Ideal O))
    (c : S → ℂ) (A : ℝ)
    (hresponse : ∀ z : rows, A ≤ ‖ordinaryPolynomial S c z.val‖ ^ 2) :
    (rows.card : ℝ) * A ≤ selectedNorm rows S * ∑ I, ‖c I‖ ^ 2 := by
  calc
    _ = ∑ _z : rows, A := by simp
    _ ≤ ∑ z : rows, ‖ordinaryPolynomial S c z.val‖ ^ 2 :=
      Finset.sum_le_sum fun z _ => hresponse z
    _ ≤ _ := ordinaryPolynomial_energy rows S c

/-- The analytic norm interface needed by the detector. The row set is fixed
before the arbitrary ordinary source set; products need not be squarefree.
The upper scale is an explicit physical polynomial range, not just `U`.
For the full application its exponent must include
`detectorAuxiliarySourceCap P_requested A`, rather than only the plain length. -/
def SelectedAllSourceNormBound (rows : Finset O) (U δ K Xmax : ℝ) : Prop :=
  0 ≤ K ∧ ∀ (X : ℝ) (S : Finset (Ideal O)), 1 ≤ X → X ≤ Xmax →
    (∀ I ∈ S, (I.absNorm : ℝ) ≤ X) →
    selectedNorm rows S ≤ K * (X + U ^ (1-δ) * X ^ δ)

/-- The norm's auxiliary source range includes the amplification crossing.
It is fixed before the later physical height parameter. -/
def detectorAuxiliarySourceCap (P_requested A : ℝ) : ℝ :=
  max P_requested (3*A) + 1

/-- Required early scalar error budget for the joint energy. The `Pmax*η`
term pays the changing zero-slope coefficient of the source scale. -/
def detectorMeshError (sstar Mmax Pmax Eamp η : ℝ) : ℝ :=
  (1+Mmax/(3*sstar))*Eamp + ((24/25)*Mmax+Pmax)*η

/-- Absolute amplitude and slope errors can be chosen before the number of
slots. Only the later per-slot precision depends on that finite number. -/
theorem exists_early_detector_precision (sstar Mmax Pmax loss : ℝ)
    (hs : 0 < sstar) (hM : 0 ≤ Mmax) (hP : 0 ≤ Pmax) (hloss : 0 < loss) :
    ∃ Eamp : ℝ, 0 < Eamp ∧ ∃ η : ℝ, 0 < η ∧
      detectorMeshError sstar Mmax Pmax Eamp η < loss ∧
      ∀ N : ℕ, ∃ precision : ℝ, 0 < precision ∧ (N : ℝ)*precision ≤ η := by
  let C₁ := 1+Mmax/(3*sstar)
  let C₂ := (24/25)*Mmax+Pmax
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  let Eamp := loss/(4*C₁)
  let η := loss/(4*(C₂+1))
  have hEamp : 0 < Eamp := by dsimp [Eamp]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hfirst : C₁*Eamp = loss/4 := by dsimp [Eamp]; field_simp
  have hsecond : (C₂+1)*η = loss/4 := by dsimp [η]; field_simp
  refine ⟨Eamp, hEamp, η, hη, ?_, ?_⟩
  · change C₁*Eamp+C₂*η < loss
    rw [hfirst]
    nlinarith
  · intro N
    refine ⟨η/((N : ℝ)+1), by positivity, ?_⟩
    calc
      _ ≤ ((N : ℝ)+1)*(η/((N : ℝ)+1)) := by gcongr; linarith
      _ = η := by field_simp

theorem ordinaryPolynomial_count_of_allSourceNorm
    (rows : Finset O) (S : Finset (Ideal O)) (c : S → ℂ)
    (U δ K Xmax X A : ℝ) (hbound : SelectedAllSourceNormBound rows U δ K Xmax)
    (hX : 1 ≤ X) (hXmax : X ≤ Xmax)
    (hnorm : ∀ I ∈ S, (I.absNorm : ℝ) ≤ X)
    (hresponse : ∀ z : rows, A ≤ ‖ordinaryPolynomial S c z.val‖ ^ 2) :
    (rows.card : ℝ) * A ≤
      K * (X + U ^ (1-δ) * X ^ δ) * ∑ I, ‖c I‖ ^ 2 := by
  exact (ordinaryPolynomial_count rows S c A hresponse).trans
    (mul_le_mul_of_nonneg_right (hbound.2 X S hX hXmax hnorm)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- The two original polynomials share exactly the zero, character, and
frequency of the supplied OAI witness. Its dyadic index still ranges up to
`ceil (2 * U^21)`. -/
def witnessInverse {Label : Type*} {χ : Label → Character}
    {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) : ℂ :=
  polynomial (χ w.label) true
    (inverseProfile HeckeDetectorProfiles.cutoff HeckeDetectorDyadicProfiles.positiveAnnular
      (U ^ tstar) (U ^ w.r)) (U ^ w.r) w.zero.re w.frequency

def witnessPlain {Label : Type*} {χ : Label → Character}
    {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) : ℂ :=
  polynomial (χ w.label) false HeckeDetectorDyadicProfiles.positiveAnnular
    (U ^ w.m) w.zero.re w.frequency

/-- All three lower responses come from the same actual witness, not three
independently selected zeros or heights. Buffers are displayed explicitly. -/
theorem witness_three_responses {Label : Type*} {χ : Label → Character}
    {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 0 < U) :
    U ^ ((2*a-1)*w.r-2*ε) ≤ ‖witnessInverse w‖ ^ 2 ∧
    U ^ ((2*a-1)*(2*w.m)-4*ε) ≤ ‖witnessPlain w ^ 2‖ ^ 2 ∧
    U ^ ((2*a-1)*(w.r+w.m)-4*ε) ≤
      ‖witnessInverse w * witnessPlain w‖ ^ 2 := by
  have hM : U ^ ((2*a-1)*w.r-2*ε) ≤ ‖witnessInverse w‖ ^ 2 := w.inverse_spike
  have hS : U ^ ((2*a-1)*w.m-2*ε) ≤ ‖witnessPlain w‖ ^ 2 := w.plain_spike
  refine ⟨hM, ?_, ?_⟩
  · calc
      _ = U ^ ((2*a-1)*w.m-2*ε) * U ^ ((2*a-1)*w.m-2*ε) := by
        rw [← Real.rpow_add hU]
        congr 1
        ring
      _ ≤ (‖witnessPlain w‖ ^ 2) * (‖witnessPlain w‖ ^ 2) :=
        mul_self_le_mul_self (Real.rpow_nonneg hU.le _) hS
      _ = _ := by rw [norm_pow]; ring
  · calc
      _ = U ^ ((2*a-1)*w.r-2*ε) * U ^ ((2*a-1)*w.m-2*ε) := by
        rw [← Real.rpow_add hU]
        congr 1
        ring
      _ ≤ (‖witnessInverse w‖ ^ 2) * (‖witnessPlain w‖ ^ 2) :=
        mul_le_mul hM hS (Real.rpow_nonneg hU.le _) (sq_nonneg _)
      _ = _ := by rw [norm_mul, mul_pow]

/-- The product constraint is used with its real finite-detector buffers.
No exact unbuffered assertion `r ≤ 1`, `m ≤ 1/2` is substituted here. -/
theorem supported_witness_lengths {Label : Type*} {χ : Label → Character}
    {U a ε T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ U a ε 1 T allowance i) :
    w.r ≤ 1+ε ∧ w.m ≤ 1/2+75*ε ∧ 1-ε ≤ w.r+w.m ∧ 0 ≤ w.m := by
  refine ⟨w.inverse_length_upper, w.plain_length_upper, ?_, w.plain_length_lower⟩
  linarith [w.product_length_lower]

/-- One-sided stability of each word's count exponent in its length. -/
theorem wordEnvelope_length_error {ν δ w v L : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (1001/2000 : ℝ) ν)
    (hL : |w-v| ≤ L) :
    wordEnvelope ν δ w ≤ wordEnvelope ν δ v + (7/20)*L := by
  have hlow : -L ≤ w-v := (abs_le.mp hL).1
  have hhigh : w-v ≤ L := (abs_le.mp hL).2
  have hLp : 0 ≤ L := (abs_nonneg _).trans hL
  have hb0 : 0 ≤ 1-ν := by linarith [hν.2]
  have hb1 : 1-ν ≤ 7/20 := by linarith [hν.1]
  have ha0 : 0 ≤ ν-δ := by linarith [hδ.2]
  have ha1 : ν-δ ≤ 7/20 := by linarith [hν.2, hδ.1]
  have hble := mul_le_mul_of_nonneg_left hhigh hb0
  have hbe := mul_le_mul_of_nonneg_right hb1 hLp
  have hale := mul_le_mul_of_nonneg_left hlow ha0
  have hae := mul_le_mul_of_nonneg_right ha1 hLp
  have hb := le_max_left ((1-ν)*v) ((1-δ)-(ν-δ)*v)
  have ha := le_max_right ((1-ν)*v) ((1-δ)-(ν-δ)*v)
  unfold wordEnvelope at *
  exact max_le (by nlinarith) (by nlinarith)

/-- The actual finite detector has buffered length inequalities. Clipping the
plain length and repairing the inverse length loses at most `53 ε` in the
three-word exponent. This is an explicit error, not an unbuffered shortcut. -/
theorem buffered_three_word_min_le {ν δ r m ε : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (1001/2000 : ℝ) ν) (hε : 0 ≤ ε)
    (hm0 : 0 ≤ m) (hr : r ≤ 1+ε) (hm : m ≤ 1/2+75*ε)
    (hrm : 1-ε ≤ r+m) :
    min (wordEnvelope ν δ r)
      (min (wordEnvelope ν δ (2*m))
        (wordEnvelope ν δ (r+m))) ≤
      jointCountExponent ν δ + 53*ε := by
  let m' := min m (1/2)
  let r' := max (min r 1) (1-m')
  have hm'0 : 0 ≤ m' := le_min hm0 (by norm_num)
  have hm'1 : m' ≤ 1/2 := min_le_right _ _
  have hm'm : m' ≤ m := min_le_left _ _
  have hmm' : m-75*ε ≤ m' := le_min (by linarith) (by linarith)
  have hr'1 : r' ≤ 1 := max_le (min_le_right _ _) (by linarith)
  have hr'0 : 0 ≤ r' := (show 0 ≤ 1-m' by linarith).trans (le_max_right _ _)
  have hr'm' : 1 ≤ r'+m' := by linarith [le_max_right (min r 1) (1-m')]
  have hrr' : r-ε ≤ r' := (le_min (by linarith) (by linarith)).trans (le_max_left _ _)
  have hr'r : r' ≤ r+76*ε := max_le ((min_le_left _ _).trans (by linarith)) (by linarith)
  have hmr : |m-m'| ≤ 75*ε := abs_le.mpr ⟨by linarith, by linarith⟩
  have hrr : |r-r'| ≤ 76*ε := abs_le.mpr ⟨by linarith, by linarith⟩
  have htwo : |2*m-2*m'| ≤ 150*ε := abs_le.mpr ⟨by linarith [abs_le.mp hmr |>.1],
    by linarith [abs_le.mp hmr |>.2]⟩
  have hsum : |(r+m)-(r'+m')| ≤ 151*ε := abs_le.mpr
    ⟨by linarith [(abs_le.mp hrr).1, (abs_le.mp hmr).1],
      by linarith [(abs_le.mp hrr).2, (abs_le.mp hmr).2]⟩
  have h1 := wordEnvelope_length_error hν hδ hrr
  have h2 := wordEnvelope_length_error hν hδ htwo
  have h3 := wordEnvelope_length_error hν hδ hsum
  have hgood := RefinedPrice.three_word_min_le hν hδ hr'0 hm'0 hr'1 hm'1 hr'm'
  have he1 : wordEnvelope ν δ r ≤ wordEnvelope ν δ r'+53*ε := by
    linarith
  have he2 : wordEnvelope ν δ (2*m) ≤
      wordEnvelope ν δ (2*m')+53*ε := by linarith
  have he3 : wordEnvelope ν δ (r+m) ≤
      wordEnvelope ν δ (r'+m')+53*ε := by linarith
  calc
    _ ≤ min (wordEnvelope ν δ r'+53*ε)
        (min (wordEnvelope ν δ (2*m')+53*ε)
          (wordEnvelope ν δ (r'+m')+53*ε)) := min_le_min he1 (min_le_min he2 he3)
    _ = min (wordEnvelope ν δ r')
        (min (wordEnvelope ν δ (2*m'))
          (wordEnvelope ν δ (r'+m'))) + 53*ε := by simp only [min_add_add_right]
    _ ≤ _ := by linarith

/-- The squared plain word and mixed word are the full merged ordinary
polynomials. The row feature is unchanged in both products. -/
theorem detector_three_words_eq (χ : Character) (base : Ideal O → ℂ) (z : O)
    (hrow : ∀ I : Ideal O, idealCoeff χ I = base I * idealRowHom z I)
    (WM WS : ℝ → ℂ) (D N σ freq : ℝ) (SM SS : Finset (Ideal O))
    (hM : ∀ I : Ideal O, I ≠ 0 → WM ((I.absNorm : ℝ)/D) ≠ 0 → I ∈ SM)
    (hS : ∀ I : Ideal O, I ≠ 0 → WS ((I.absNorm : ℝ)/N) ≠ 0 → I ∈ SS) :
    let cM : SM → ℂ := fun I => detectorCoefficient base true WM D σ freq I.val
    let cS : SS → ℂ := fun I => detectorCoefficient base false WS N σ freq I.val
    polynomial χ true WM D σ freq = ordinaryPolynomial SM cM z ∧
    (polynomial χ false WS N σ freq)^2 =
      ordinaryPolynomial (idealProductSources SS SS) (idealConvolution SS SS cS cS) z ∧
    polynomial χ true WM D σ freq * polynomial χ false WS N σ freq =
      ordinaryPolynomial (idealProductSources SM SS) (idealConvolution SM SS cM cS) z := by
  dsimp only
  have hM' := detector_polynomial_eq χ base z hrow true WM D σ freq SM hM
  have hS' := detector_polynomial_eq χ base z hrow false WS N σ freq SS hS
  refine ⟨hM', ?_, ?_⟩
  · rw [hS', pow_two, ordinaryPolynomial_mul]
  · rw [hM', hS', ordinaryPolynomial_mul]

/-- The whole finite three-word count on one fixed character/dyadic fiber.
The inputs are upper moments of the actual three polynomials, which the
coefficient/norm and Sobolev lemmas above and below supply. They are not a
postulated zero count. The two length labels still range over the genuine
`dyadicLength U`, with terminal length `U^21`.
-/
theorem actual_three_word_fiber_count {Row Label : Type*}
    (rows : Finset Row) (χ : Row → Label → Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1 < U)
    (w : ∀ u, Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u ∈ rows, (w u).label = label)
    (hJ : ∀ u ∈ rows, (w u).left = J) (hK : ∀ u ∈ rows, (w u).right = K)
    (CM CSS CMS bM bSS bMS : ℝ)
    (hM : let r := Real.logb U ((2 : ℝ)^J.val)
      ∑ u ∈ rows, ‖polynomial (χ u label) true
        (inverseProfile HeckeDetectorProfiles.cutoff HeckeDetectorDyadicProfiles.positiveAnnular
          (U^tstar) (U^r)) (U^r) (w u).zero.re (w u).frequency‖^2 ≤ CM*U^bM)
    (hSS : let m := Real.logb U ((2 : ℝ)^K.val)
      ∑ u ∈ rows, ‖polynomial (χ u label) false HeckeDetectorDyadicProfiles.positiveAnnular
        (U^m) (w u).zero.re (w u).frequency ^ 2‖^2 ≤ CSS*U^bSS)
    (hMS : let r := Real.logb U ((2 : ℝ)^J.val)
      let m := Real.logb U ((2 : ℝ)^K.val)
      ∑ u ∈ rows, ‖polynomial (χ u label) true
        (inverseProfile HeckeDetectorProfiles.cutoff HeckeDetectorDyadicProfiles.positiveAnnular
          (U^tstar) (U^r)) (U^r) (w u).zero.re (w u).frequency *
        polynomial (χ u label) false HeckeDetectorDyadicProfiles.positiveAnnular
          (U^m) (w u).zero.re (w u).frequency‖^2 ≤ CMS*U^bMS) :
    let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^K.val)
    (rows.card : ℝ) ≤ min (CM * U^(bM-((2*a-1)*r-2*ε)))
      (min (CSS * U^(bSS-((2*a-1)*(2*m)-4*ε)))
        (CMS * U^(bMS-((2*a-1)*(r+m)-4*ε)))) := by
  let r := Real.logb U ((2 : ℝ)^J.val)
  let m := Real.logb U ((2 : ℝ)^K.val)
  let M (u : Row) := polynomial (χ u label) true
    (inverseProfile HeckeDetectorProfiles.cutoff HeckeDetectorDyadicProfiles.positiveAnnular
      (U^tstar) (U^r)) (U^r) (w u).zero.re (w u).frequency
  let S (u : Row) := polynomial (χ u label) false HeckeDetectorDyadicProfiles.positiveAnnular
    (U^m) (w u).zero.re (w u).frequency
  have hresponse (u : Row) (hu : u ∈ rows) :
      U^((2*a-1)*r-2*ε) ≤ ‖M u‖^2 ∧
      U^((2*a-1)*(2*m)-4*ε) ≤ ‖S u ^ 2‖^2 ∧
      U^((2*a-1)*(r+m)-4*ε) ≤ ‖M u * S u‖^2 := by
    have hr : (w u).r = r := by rw [(w u).left_exponent hU, hJ u hu]
    have hm : (w u).m = m := by rw [(w u).right_exponent hU, hK u hu]
    simpa only [witnessInverse, witnessPlain, hr, hm, hlabel u hu, M, S] using
      witness_three_responses (w u) (zero_lt_one.trans hU)
  apply le_min
  · exact HeckeDetectorRowCount.card_of_energy rows M U _ bM CM (zero_lt_one.trans hU)
      (fun u hu => (hresponse u hu).1) hM
  · apply le_min
    · exact HeckeDetectorRowCount.card_of_energy rows (fun u => S u ^ 2) U _ bSS CSS
        (zero_lt_one.trans hU) (fun u hu => (hresponse u hu).2.1) hSS
    · exact HeckeDetectorRowCount.card_of_energy rows (fun u => M u * S u) U _ bMS CMS
        (zero_lt_one.trans hU) (fun u hu => (hresponse u hu).2.2) hMS

/-- Sobolev applies to the whole mixed word on a fixed row set. Its derivative
chains contain every Leibniz term, with the same two variables in both factors.
The fixed row multiplier `P` can include a selected-set indicator or slot weight.
-/
theorem mixed_chain_rowwise {ι : Type*} (rows : Finset ι)
    (Q R : ℕ → ι → ℝ → ℝ → ℂ)
    (cq : ∀ n i, n ≤ 2 → Continuous (Function.uncurry (Q n i)))
    (cr : ∀ n i, n ≤ 2 → Continuous (Function.uncurry (R n i)))
    (qx : ∀ n i x y, n ≤ 1 →
      HasDerivAt (fun u => Q n i u y) (-Q (n+1) i x y) x)
    (rx : ∀ n i x y, n ≤ 1 →
      HasDerivAt (fun u => R n i u y) (-R (n+1) i x y) x)
    (qy : ∀ n i x y, n ≤ 1 →
      HasDerivAt (Q n i x) (Complex.I * Q (n+1) i x y) y)
    (ry : ∀ n i x y, n ≤ 1 →
      HasDerivAt (R n i x) (Complex.I * R (n+1) i x y) y)
    (P : ι → ℂ) (a b c d E : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (hE : 0 ≤ E)
    (σ freq : ι → ℝ) (hσ : ∀ i ∈ rows, σ i ∈ Set.Icc a b)
    (hf : ∀ i ∈ rows, freq i ∈ Set.Icc c d)
    (henergy : ∀ j k : ℕ, j+k ≤ 2 → ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d,
      ∑ i ∈ rows, ‖Q j i x y * R k i x y * P i‖ ^ 2 ≤ E) :
    ∑ i ∈ rows, ‖Q 0 i (σ i) (freq i) * R 0 i (σ i) (freq i) * P i‖ ^ 2 ≤
      (1+2*(b-a))*((1+2*(d-c))*(16*E)) := by
  let M (n : ℕ) (i : ι) (x y : ℝ) :=
    if n = 0 then Q 0 i x y * R 0 i x y * P i
    else if n = 1 then (Q 1 i x y * R 0 i x y + Q 0 i x y * R 1 i x y) * P i
    else (Q 2 i x y * R 0 i x y + 2 * (Q 1 i x y * R 1 i x y) +
      Q 0 i x y * R 2 i x y) * P i
  have cm (n : ℕ) (i : ι) (hn : n ≤ 2) : Continuous (Function.uncurry (M n i)) := by
    have cq0 := cq 0 i (by norm_num)
    have cq1 := cq 1 i (by norm_num)
    have cq2 := cq 2 i (by norm_num)
    have cr0 := cr 0 i (by norm_num)
    have cr1 := cr 1 i (by norm_num)
    have cr2 := cr 2 i (by norm_num)
    change Continuous (fun p : ℝ × ℝ => M n i p.1 p.2)
    change Continuous (fun p : ℝ × ℝ => Q 0 i p.1 p.2) at cq0
    change Continuous (fun p : ℝ × ℝ => Q 1 i p.1 p.2) at cq1
    change Continuous (fun p : ℝ × ℝ => Q 2 i p.1 p.2) at cq2
    change Continuous (fun p : ℝ × ℝ => R 0 i p.1 p.2) at cr0
    change Continuous (fun p : ℝ × ℝ => R 1 i p.1 p.2) at cr1
    change Continuous (fun p : ℝ × ℝ => R 2 i p.1 p.2) at cr2
    interval_cases n <;> dsimp [M] <;> fun_prop
  have dx (n : ℕ) (i : ι) (x y : ℝ) (hn : n ≤ 1) :
      HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x := by
    interval_cases n
    · convert ((qx 0 i x y (by norm_num)).mul
        (rx 0 i x y (by norm_num))).mul_const (P i) using 1
      · ext u; simp [M]
      · simp [M]; ring
    · convert (((qx 1 i x y (by norm_num)).mul (rx 0 i x y (by norm_num))).add
        ((qx 0 i x y (by norm_num)).mul (rx 1 i x y (by norm_num)))).mul_const (P i) using 1
      · ext u; simp [M]
      · simp [M]; ring
  have dy (n : ℕ) (i : ι) (x y : ℝ) (hn : n ≤ 1) :
      HasDerivAt (M n i x) (Complex.I * M (n+1) i x y) y := by
    interval_cases n
    · convert ((qy 0 i x y (by norm_num)).mul
        (ry 0 i x y (by norm_num))).mul_const (P i) using 1
      · ext u; simp [M]
      · simp [M]; ring
    · convert (((qy 1 i x y (by norm_num)).mul (ry 0 i x y (by norm_num))).add
        ((qy 0 i x y (by norm_num)).mul (ry 1 i x y (by norm_num)))).mul_const (P i) using 1
      · ext u; simp [M]
      · simp [M]; ring
  have hs2 := HeckeDetectorRowwisePlain.norm_sum_sq_le
  have hs3 (u v w : ℂ) :
      ‖u+2*v+w‖ ^ 2 ≤ 4*(‖u‖ ^ 2+2*‖v‖ ^ 2+‖w‖ ^ 2) := by
    have h1 := hs2 (u+v) (v+w)
    have h2 := hs2 u v
    have h3 := hs2 v w
    have heq : u+2*v+w = (u+v)+(v+w) := by ring
    rw [heq]
    linarith
  have he (n : ℕ) (hn : n ≤ 2) (x : ℝ) (hx : x ∈ Set.Icc a b)
      (y : ℝ) (hy : y ∈ Set.Icc c d) : ∑ i ∈ rows, ‖M n i x y‖ ^ 2 ≤ 16*E := by
    have e00 := henergy 0 0 (by norm_num) x hx y hy
    have e10 := henergy 1 0 (by norm_num) x hx y hy
    have e01 := henergy 0 1 (by norm_num) x hx y hy
    have e20 := henergy 2 0 (by norm_num) x hx y hy
    have e11 := henergy 1 1 (by norm_num) x hx y hy
    have e02 := henergy 0 2 (by norm_num) x hx y hy
    interval_cases n
    · simpa only [M, ite_true] using e00.trans (show E ≤ 16*E by linarith)
    · have hb : (∑ i ∈ rows, ‖M 1 i x y‖ ^ 2) ≤
          2*((∑ i ∈ rows, ‖Q 1 i x y * R 0 i x y * P i‖ ^ 2)+
            ∑ i ∈ rows, ‖Q 0 i x y * R 1 i x y * P i‖ ^ 2) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hid : M 1 i x y = Q 1 i x y * R 0 i x y * P i +
            Q 0 i x y * R 1 i x y * P i := by simp [M]; ring
        rw [hid]
        exact hs2 _ _
      linarith
    · have hb : (∑ i ∈ rows, ‖M 2 i x y‖ ^ 2) ≤
          4*((∑ i ∈ rows, ‖Q 2 i x y * R 0 i x y * P i‖ ^ 2)+
            2*(∑ i ∈ rows, ‖Q 1 i x y * R 1 i x y * P i‖ ^ 2)+
            ∑ i ∈ rows, ‖Q 0 i x y * R 2 i x y * P i‖ ^ 2) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro i hi
        have hid : M 2 i x y = Q 2 i x y * R 0 i x y * P i +
            2*(Q 1 i x y * R 1 i x y * P i) + Q 0 i x y * R 2 i x y * P i := by
          simp [M]; ring
        rw [hid]
        exact hs3 _ _ _
      linarith
  simpa only [M, ite_true] using HeckeDetectorRowwise.chain_rowwise
    rows M cm dx dy a b c d (16*E) hab hcd σ freq hσ hf he

/-- Actual inverse/plain product Sobolev estimate, using the derivative
formulas of the accepted ordinary Dirichlet polynomials. -/
theorem detector_mixed_rowwise {ι : Type*} (rows : Finset ι) (χ : ι → Character)
    (WM WS : ℝ → ℂ) (D N : ℝ) (hD : 0 < D) (hN : 0 < N)
    (SM SS : Finset (Ideal O))
    (hcM : ∀ J : Ideal O, J ≠ 0 → WM ((J.absNorm : ℝ)/D) ≠ 0 → J ∈ SM)
    (hcS : ∀ J : Ideal O, J ≠ 0 → WS ((J.absNorm : ℝ)/N) ≠ 0 → J ∈ SS)
    (P : ι → ℂ) (a b c d E : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (hE : 0 ≤ E)
    (σ freq : ι → ℝ) (hσ : ∀ i ∈ rows, σ i ∈ Set.Icc a b)
    (hf : ∀ i ∈ rows, freq i ∈ Set.Icc c d)
    (henergy : ∀ j k : ℕ, j+k ≤ 2 → ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d,
      ∑ i ∈ rows, ‖polynomial (χ i) true ((HeckeDetectorRowwisePolynomial.logProfile^[j]) WM)
        D x y * polynomial (χ i) false ((HeckeDetectorRowwisePolynomial.logProfile^[k]) WS)
        N x y * P i‖ ^ 2 ≤ E) :
    ∑ i ∈ rows, ‖polynomial (χ i) true WM D (σ i) (freq i) *
      polynomial (χ i) false WS N (σ i) (freq i) * P i‖ ^ 2 ≤
      (1+2*(b-a))*((1+2*(d-c))*(16*E)) := by
  let Q (n : ℕ) (i : ι) (x y : ℝ) :=
    polynomial (χ i) true ((HeckeDetectorRowwisePolynomial.logProfile^[n]) WM) D x y
  let R (n : ℕ) (i : ι) (x y : ℝ) :=
    polynomial (χ i) false ((HeckeDetectorRowwisePolynomial.logProfile^[n]) WS) N x y
  open HeckeDetectorRowwisePolynomial in
  have coverM1 := logProfile_cover WM D SM hcM
  open HeckeDetectorRowwisePolynomial in
  have coverM2 := logProfile_cover _ D SM coverM1
  open HeckeDetectorRowwisePolynomial in
  have coverS1 := logProfile_cover WS N SS hcS
  open HeckeDetectorRowwisePolynomial in
  have coverS2 := logProfile_cover _ N SS coverS1
  have cq (n : ℕ) (i : ι) (hn : n ≤ 2) : Continuous (Function.uncurry (Q n i)) := by
    interval_cases n
    · exact HeckeDetectorRowwisePolynomial.polynomial_continuous (χ i) true WM D hD SM hcM
    · exact HeckeDetectorRowwisePolynomial.polynomial_continuous (χ i) true _ D hD SM coverM1
    · exact HeckeDetectorRowwisePolynomial.polynomial_continuous (χ i) true _ D hD SM coverM2
  have cr (n : ℕ) (i : ι) (hn : n ≤ 2) : Continuous (Function.uncurry (R n i)) := by
    interval_cases n
    · exact HeckeDetectorRowwisePolynomial.polynomial_continuous (χ i) false WS N hN SS hcS
    · exact HeckeDetectorRowwisePolynomial.polynomial_continuous (χ i) false _ N hN SS coverS1
    · exact HeckeDetectorRowwisePolynomial.polynomial_continuous (χ i) false _ N hN SS coverS2
  have qx (n : ℕ) (i : ι) (x y : ℝ) (hn : n ≤ 1) :
      HasDerivAt (fun u => Q n i u y) (-Q (n+1) i x y) x := by
    interval_cases n
    · exact HeckeDetectorRowwisePolynomial.polynomial_sigma_deriv (χ i) true WM D x y hD SM hcM
    · exact HeckeDetectorRowwisePolynomial.polynomial_sigma_deriv (χ i) true _ D x y hD SM coverM1
  have rx (n : ℕ) (i : ι) (x y : ℝ) (hn : n ≤ 1) :
      HasDerivAt (fun u => R n i u y) (-R (n+1) i x y) x := by
    interval_cases n
    · exact HeckeDetectorRowwisePolynomial.polynomial_sigma_deriv (χ i) false WS N x y hN SS hcS
    · exact HeckeDetectorRowwisePolynomial.polynomial_sigma_deriv (χ i) false _ N x y hN SS coverS1
  have qy (n : ℕ) (i : ι) (x y : ℝ) (hn : n ≤ 1) :
      HasDerivAt (Q n i x) (Complex.I * Q (n+1) i x y) y := by
    interval_cases n
    · exact HeckeDetectorRowwisePolynomial.polynomial_freq_deriv (χ i) true WM D x y hD SM hcM
    · exact HeckeDetectorRowwisePolynomial.polynomial_freq_deriv (χ i) true _ D x y hD SM coverM1
  have ry (n : ℕ) (i : ι) (x y : ℝ) (hn : n ≤ 1) :
      HasDerivAt (R n i x) (Complex.I * R (n+1) i x y) y := by
    interval_cases n
    · exact HeckeDetectorRowwisePolynomial.polynomial_freq_deriv (χ i) false WS N x y hN SS hcS
    · exact HeckeDetectorRowwisePolynomial.polynomial_freq_deriv (χ i) false _ N x y hN SS coverS1
  exact mixed_chain_rowwise rows Q R cq cr qx rx qy ry P a b c d E hab hcd hE σ freq hσ hf henergy

/-- The actual mixed-word counterpart of OAI's inverse and squared-plain
fiber energy theorems. Selection is fixed throughout the Sobolev argument. -/
theorem detector_mixed_witness_energy {Row Label : Type*}
    (rows : Finset Row) (χ : Row → Label → Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (ha : 0 ≤ a)
    (w : ∀ u, Witness (χ u) U a ε tstar T allowance i) (label : Label)
    (WM WS : ℝ → ℂ) (D N : ℝ) (hD : 0 < D) (hN : 0 < N)
    (SM SS : Finset (Ideal O))
    (hcM : ∀ J : Ideal O, J ≠ 0 → WM ((J.absNorm : ℝ)/D) ≠ 0 → J ∈ SM)
    (hcS : ∀ J : Ideal O, J ≠ 0 → WS ((J.absNorm : ℝ)/N) ≠ 0 → J ∈ SS)
    (P : Row → ℂ) (E height : ℝ) (hE : 0 ≤ E) (hh : 0 ≤ height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T ≤ height)
    (hraw : ∀ j k : ℕ, j+k ≤ 2 → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-height) height,
      ∑ u ∈ rows, ‖polynomial (χ u label) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[j]) WM) D s t *
        polynomial (χ u label) false ((HeckeDetectorRowwisePolynomial.logProfile^[k]) WS)
          N s t * P u‖ ^ 2 ≤ E) :
    ∑ u ∈ rows, ‖polynomial (χ u label) true WM D (w u).zero.re (w u).frequency *
      polynomial (χ u label) false WS N (w u).zero.re (w u).frequency * P u‖ ^ 2 ≤
      192*(1+height)*E := by
  have hσ (u : Row) (_hu : u ∈ rows) : (w u).zero.re ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨ha.trans (w u).zero_lower, (w u).real_part_upper⟩
  have hf (u : Row) (_hu : u ∈ rows) : (w u).frequency ∈ Set.Icc (-height) height :=
    abs_le.mp ((w u).frequency_bound.trans hfreq)
  have h := detector_mixed_rowwise rows (fun u => χ u label) WM WS D N hD hN SM SS hcM hcS
    P 0 1 (-height) height E (by norm_num) (by linarith) hE
    (fun u => (w u).zero.re) (fun u => (w u).frequency) hσ hf hraw
  exact h.trans (by nlinarith)

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.detector_polynomial_eq_fixedBase
#print axioms Qrh.JointDetector.ordinaryPolynomial_mul
#print axioms Qrh.JointDetector.idealConvolution_mass_small_power
#print axioms Qrh.JointDetector.ordinaryPolynomial_count
#print axioms Qrh.JointDetector.witness_three_responses
#print axioms Qrh.JointDetector.detector_three_words_eq
#print axioms Qrh.JointDetector.detector_mixed_rowwise
#print axioms Qrh.JointDetector.detectorCoefficient_mass
#print axioms Qrh.JointDetector.detector_raw_product_energy
#print axioms Qrh.JointDetector.buffered_three_word_min_le
#print axioms Qrh.JointDetector.actual_three_word_fiber_count
#print axioms Qrh.JointDetector.exists_early_detector_precision
#print axioms Qrh.JointDetector.detector_mixed_witness_energy
