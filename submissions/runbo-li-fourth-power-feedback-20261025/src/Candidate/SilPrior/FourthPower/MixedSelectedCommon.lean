/- Copyright (c) 2026 Sil. Apache-2.0.
Finite selected-block Gauss separation. The only cross-mask is coprimality,
and it becomes the natural zero of the moving cubic character. The phase
is separated by the unchanged baseline ray expansion.

 The actual original-tuple factorization
into the displayed selected scalar and residual coefficient is a separate
instantiation obligation; it is not asserted here.
-/
import Candidate.SilPrior.FourthPower.MixedPhysicalTransfer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstColumns

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.MixedSelectedCommon
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss ProbePhysical
open CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation
open CenteredMomentFirstColumns CenteredMomentFixedRay RayFourExpansion
open CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- The FULL supplier partition supplies `IsCoprime seed D`. A partial
supplier allocation is insufficient. The old mask is preserved on n. -/
theorem surviving_seed_iff (f seed D n : Id) (hf : f ≠ 0)
    (hseed : IsCoprime seed D) : f*seed ∣ f*D*n ↔ seed ∣ n := by
  rw [mul_assoc, mul_dvd_mul_iff_left hf]
  constructor
  · exact hseed.dvd_of_dvd_mul_left
  · intro h
    exact h.trans (dvd_mul_left n D)

/-- There is no selected block, selected assignment or frequency argument
in this vector. The ray label is fixed before averaging the selected block. -/
def commonCoefficient {ι : Type*} (a : ι → O) (B : ι → ℂ)
    (ξ : RayCharacter) (v : ι) : ℂ := B v * rayCharacter ξ (a v)

def selectedRow {ι : Type*} (V : Finset ι) (a : ι → O)
    (ha : ∀ v, Supported (Ideal.span {a v})) (A : ℂ) (B : ι → ℂ)
    (d : O) (hd : Supported (Ideal.span {d})) (k : O) : ℂ :=
  ∑ v ∈ V, A * B v * (if IsCoprime d (a v) then
    gaussRow (d*a v) (supported_mul_elements _ _ hd (ha v)) k else 0)

theorem normalized_coprime_product (d a : O)
    (hd : Supported (Ideal.span {d})) (ha : Supported (Ideal.span {a}))
    (hpd : goodLambda^2 ∣ d-1) (hpa : goodLambda^2 ∣ a-1)
    (hcop : IsCoprime d a) (k : O) :
    gaussRow (d*a) (supported_mul_elements _ _ hd ha) k =
      sexticReciprocityPhase d a * (idealRowHom d (Ideal.span {a}))^2 *
        gaussRow d hd k * gaussRow a ha k := by
  have hroot : (Real.sqrt (Ideal.absNorm (Ideal.span {d*a}) : ℝ) : ℂ) =
      (Real.sqrt (Ideal.absNorm (Ideal.span {d}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ) := by
    simp only [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul,
      Real.sqrt_mul (by positivity : 0 ≤ (Ideal.absNorm (Ideal.span {d}) : ℝ)),
      Complex.ofReal_mul]
  unfold gaussRow
  rw [sexticGauss_coprime_product d a hd ha hcop k, hroot,
    idealRowHom_primary_reciprocity d a hpd hpa hd ha]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The noncoprime branch is proved from the actual character's sixth
power, not removed by an inequality inside a squared sum. -/
theorem moving_square_zero (d a : O) (ha : Supported (Ideal.span {a}))
    (hcop : ¬IsCoprime d a) : (idealRowHom d (Ideal.span {a}))^2 = 0 := by
  have h6 : (idealRowHom d (Ideal.span {a}))^6 = 0 := by
    rw [← idealRowHom_argument_pow d 6 _ ha, idealRowHom_sixth_eq_mask d a ha]
    simp [coprimalityMask, hcop]
  rw [eq_zero_of_pow_eq_zero h6, zero_pow (by decide : 2 ≠ 0)]

theorem masked_product_rays (d a : O)
    (hd : Supported (Ideal.span {d})) (ha : Supported (Ideal.span {a}))
    (hpd : goodLambda^2 ∣ d-1) (hpa : goodLambda^2 ∣ a-1) (k : O) :
    (if IsCoprime d a then
      gaussRow (d*a) (supported_mul_elements _ _ hd ha) k else 0) =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff firstPhaseTable χ ξ * rayCharacter χ d * rayCharacter ξ a *
          (idealRowHom d (Ideal.span {a}))^2 * gaussRow d hd k * gaussRow a ha k := by
  by_cases hcop : IsCoprime d a
  · rw [if_pos hcop, normalized_coprime_product d a hd ha hpd hpa hcop k,
      firstPhaseTable_expansion d a hd ha]
    simp only [Finset.sum_mul]
  · simp [hcop, moving_square_zero d a ha hcop]

/-- Exact common-vector dictionary, before Cauchy or any norm estimate.
The input has the explicit separated coefficient A * B(v). -/
theorem selected_row_rays {ι : Type*} (V : Finset ι) (a : ι → O)
    (ha : ∀ v, Supported (Ideal.span {a v}))
    (hpa : ∀ v, goodLambda^2 ∣ a v-1) (A : ℂ) (B : ι → ℂ)
    (d : O) (hd : Supported (Ideal.span {d})) (hpd : goodLambda^2 ∣ d-1) (k : O) :
    selectedRow V a ha A B d hd k =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff firstPhaseTable χ ξ * (A * rayCharacter χ d * gaussRow d hd k) *
          (∑ v ∈ V, commonCoefficient a B ξ v *
            (idealRowHom d (Ideal.span {a v}))^2 * gaussRow (a v) (ha v) k) := by
  have hrow (v : ι) := masked_product_rays d (a v) hd (ha v) hpd (hpa v) k
  unfold selectedRow commonCoefficient
  simp_rw [hrow]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ _
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem selected_row_fourth {ι : Type*} (V : Finset ι) (a : ι → O)
    (ha : ∀ v, Supported (Ideal.span {a v}))
    (hpa : ∀ v, goodLambda^2 ∣ a v-1) (A : ℂ) (B : ι → ℂ)
    (hf : ∀ v ∈ V, B v ≠ 0 → GaussTransfer.FifthFree (a v))
    (d : O) (hd : Supported (Ideal.span {d})) (hpd : goodLambda^2 ∣ d-1) (k : O) :
    selectedRow V a ha A B d hd k =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff firstPhaseTable χ ξ * (A * rayCharacter χ d * gaussRow d hd k) *
          gaussPolynomial V a ha (commonCoefficient a B ξ) (d^4*k) := by
  rw [selected_row_rays V a ha hpa A B d hd hpd k]
  apply Finset.sum_congr rfl
  intro χ _
  apply Finset.sum_congr rfl
  intro ξ _
  have hfξ : ∀ v ∈ V, commonCoefficient a B ξ v ≠ 0 →
      GaussTransfer.FifthFree (a v) := by
    intro v hv hb
    apply hf v hv
    intro hz
    exact hb (by simp [commonCoefficient, hz])
  rw [MixedPhysicalTransfer.sparse_fourth_power V a ha (commonCoefficient a B ξ) hfξ d k]

/-- A whole selected assignment family uses the SAME residual vector for
each fixed ξ. In particular grouping assignments by their product d does
not require changing that vector. All selected coefficients remain exact. -/
theorem selected_family_fourth {τ ι : Type*} (T : Finset τ) (V : Finset ι)
    (a : ι → O) (ha : ∀ v, Supported (Ideal.span {a v}))
    (hpa : ∀ v, goodLambda^2 ∣ a v-1) (A : τ → ℂ) (B : ι → ℂ)
    (hf : ∀ v ∈ V, B v ≠ 0 → GaussTransfer.FifthFree (a v))
    (d : τ → O) (hd : ∀ t, Supported (Ideal.span {d t}))
    (hpd : ∀ t, goodLambda^2 ∣ d t-1) (k : O) :
    (∑ t ∈ T, selectedRow V a ha (A t) B (d t) (hd t) k) =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        ∑ t ∈ T, (A t * rayCharacter χ (d t) * gaussRow (d t) (hd t) k) *
          gaussPolynomial V a ha (commonCoefficient a B ξ) ((d t)^4*k) := by
  have hrow (t : τ) := selected_row_fourth V a ha hpa (A t) B hf (d t) (hd t) (hpd t) k
  simp_rw [hrow]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ _
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- The old artificial mask can be incorporated into B only after the
complete supplier partition has proved the explicit coprimality premise. -/
theorem seeded_row_eq {ι : Type*} (V : Finset ι) (a : ι → O)
    (ha : ∀ v, Supported (Ideal.span {a v})) (A : ℂ) (B : ι → ℂ)
    (f seed : Id) (hf : f ≠ 0) (d : O) (hd : Supported (Ideal.span {d}))
    (hseed : IsCoprime seed (Ideal.span {d})) (k : O) :
    (∑ v ∈ V, (if f*seed ∣ f*Ideal.span {d}*Ideal.span {a v} then A * B v else 0) *
      (if IsCoprime d (a v) then
        gaussRow (d*a v) (supported_mul_elements _ _ hd (ha v)) k else 0)) =
      selectedRow V a ha A (fun v => if seed ∣ Ideal.span {a v} then B v else 0) d hd k := by
  unfold selectedRow
  apply Finset.sum_congr rfl
  intro v hv
  rw [surviving_seed_iff f seed (Ideal.span {d}) (Ideal.span {a v}) hf hseed]
  by_cases hs : seed ∣ Ideal.span {a v} <;>
    simp only [hs, ite_true, ite_false, mul_zero, zero_mul]

theorem primary_supported (I : Id) (hI : Supported I) :
    Supported (Ideal.span {primaryGenerator I}) := by
  rw [primary_span_supported I hI]
  exact hI

def idealGauss (I : Id) (hI : Supported I) (k : O) : ℂ :=
  gaussRow (primaryGenerator I) (primary_supported I hI) k

/-- The ideal-valued version starts with the original product generator,
and the original artificial mask. `primaryGenerator_mul` is an exact
identity, so no unit or ray phase is silently discarded at this step.
The surviving seed and all residual factors remain in the common vector. -/
theorem ideal_seeded_selected_row_fourth {ι : Type*} (V : Finset ι)
    (n : ι → Id) (hn : ∀ v, Supported (n v)) (A : ℂ) (B : ι → ℂ)
    (f seed D : Id) (hf : f ≠ 0) (hD : Supported D)
    (hseed : IsCoprime seed D)
    (hfree : ∀ v ∈ V, (if seed ∣ n v then B v else 0) ≠ 0 →
      SexticSieve.PowerFree 5 (n v)) (k : O) :
    (∑ v ∈ V, (if f*seed ∣ f*D*n v then A*B v else 0) *
      (if IsCoprime D (n v) then
        idealGauss (D*n v) ((supported_mul_iff D (n v)).mpr ⟨hD, hn v⟩) k else 0)) =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff firstPhaseTable χ ξ *
          (A * rayCharacter χ (primaryGenerator D) * idealGauss D hD k) *
            gaussPolynomial V (fun v => primaryGenerator (n v))
              (fun v => primary_supported (n v) (hn v))
              (commonCoefficient (fun v => primaryGenerator (n v))
                (fun v => if seed ∣ n v then B v else 0) ξ)
              ((primaryGenerator D)^4*k) := by
  have hcop (v : ι) : IsCoprime (primaryGenerator D) (primaryGenerator (n v)) ↔
      IsCoprime D (n v) := by
    rw [← Ideal.isCoprime_span_singleton_iff,
      primary_span_supported D hD, primary_span_supported (n v) (hn v)]
  have he : (∑ v ∈ V, (if f*seed ∣ f*D*n v then A*B v else 0) *
      (if IsCoprime D (n v) then
        idealGauss (D*n v) ((supported_mul_iff D (n v)).mpr ⟨hD, hn v⟩) k else 0)) =
      selectedRow V (fun v => primaryGenerator (n v))
        (fun v => primary_supported (n v) (hn v)) A
        (fun v => if seed ∣ n v then B v else 0)
        (primaryGenerator D) (primary_supported D hD) k := by
    unfold selectedRow idealGauss
    apply Finset.sum_congr rfl
    intro v hv
    rw [surviving_seed_iff f seed D (n v) hf hseed, hcop v]
    simp only [primaryGenerator_mul]
    by_cases hs : seed ∣ n v <;>
      simp only [hs, ite_true, ite_false, mul_zero, zero_mul]
  rw [he]
  apply selected_row_fourth V _ _
    (fun v => (primaryGenerator_spec (n v)
      (supported_primaryGenerator_ne_zero (n v) (hn v))).2) A _ _
    (primaryGenerator D) (primary_supported D hD)
    (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).2 k
  intro v hv hb
  apply KernelWholeColumns.element_fifth_free
  rw [primary_span_supported (n v) (hn v)]
  exact hfree v hv hb

end
end Candidate.SilPrior.FourthPower.MixedSelectedCommon
