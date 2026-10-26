/- Copyright (c) 2026 Sil. Apache-2.0.
Actual supplier zeros retained for the OUTER original-frequency branch.
No fourth-power transfer, new energy assumption or root-count premise.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedSupplierPositive
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ExceptionalPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedSupplierOuterActive
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ConcretePrimeRowBridge CenteredMomentFixedRay RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentChildRows
open MixedSupplierKernel MixedSupplierFourthRow MixedSupplierPositive
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

/-- These are necessary actual scalar gates. In particular this predicate
has no physical frequency, height, or reciprocity-ray argument. -/
structure SelectedActive (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) : Prop where
  gate : selectedGate q.R (frozenProduct q x) (selectedProduct q y)
  weight : selectedWeight q y ≠ 0
  support : Supported (frozenProduct q x * selectedProduct q y)
  coefficient : idealCoeff τ (frozenProduct q x * selectedProduct q y) ≠ 0

theorem scalar_active (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (t : ℝ) (k : O) (χ : RayCharacter)
    (hs : selectedScalar q x y τ t k χ ≠ 0) : SelectedActive q x y τ := by
  refine ⟨?_,?_,?_,?_⟩
  · by_contra h
    exact hs (by simp only [selectedScalar,if_neg h,zero_mul])
  · intro h
    exact hs (by simp only [selectedScalar,h,mul_zero,zero_mul])
  · exact (supported_mul_iff _ _).mpr (scalar_supported q x y τ t k χ hs)
  · intro h
    exact hs (by simp only [selectedScalar,heightCoeff,h,zero_mul,mul_zero])

/-- Off any retained gate the actual scalar vanishes identically, at all
frequencies, heights, and finite rays. -/
theorem scalar_zero_off_active (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (h : ¬SelectedActive q x y τ)
    (t : ℝ) (k : O) (χ : RayCharacter) : selectedScalar q x y τ t k χ = 0 := by
  by_contra hn
  exact h (scalar_active q x y τ t k χ hn)

theorem active_coefficients (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (h : SelectedActive q x y τ) :
    idealCoeff τ (frozenProduct q x) ≠ 0 ∧
      idealCoeff τ (selectedProduct q y) ≠ 0 := by
  have he := h.coefficient
  rw [map_mul] at he
  exact mul_ne_zero_iff.mp he

/-- Applies to every divisor of D, in particular each genuinely selected
prime. It concerns the ORIGINAL fixed character, not a D-dependent twist. -/
theorem active_selected_divisor_coprime (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (h : SelectedActive q x y τ) (P : Id)
    (hP : P ∣ selectedProduct q y) : IsCoprime τ.modulus P := by
  have hc := (CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff τ
    (selectedProduct q y)).mp (active_coefficients q x y τ h).2
  exact hc.2.symm.of_isCoprime_of_dvd_right hP

theorem active_selected_prime_coprime (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (h : SelectedActive q x y τ) (j : q.J) :
    IsCoprime τ.modulus (y j).val :=
  active_selected_divisor_coprime q x y τ h (y j).val
    (Finset.dvd_prod_of_mem (fun i : q.J => (y i).val) (Finset.mem_univ j))

/-- Fixed rays are handled only at Q-good primes. Supported D by itself
does NOT imply that D is coprime to Q. -/
theorem active_child_divisor_coprime (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (h : SelectedActive q x y τ) (ξ : RayCharacter) (Q P : Id)
    (hQ : Q ≤ Ideal.span {(72 : O)}) (hQP : IsCoprime Q P)
    (hP : P ∣ selectedProduct q y) : IsCoprime (childCharacter τ ξ).modulus P :=
  childCharacter_coprime τ ξ Q P hQ hQP
    (active_selected_divisor_coprime q x y τ h P hP)

/-- The scalar majorant keeps every frequency-independent natural zero.
This is deliberately stronger than merely norm(selectedWeight)^2. -/
def selectedPositiveWeight (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) : ℝ :=
  if SelectedActive q x y τ then ‖selectedWeight q y‖^2 else 0

theorem selected_positive_nonneg (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) : 0 ≤ selectedPositiveWeight q x y τ := by
  unfold selectedPositiveWeight
  split_ifs <;> positivity

theorem selected_positive_active (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (h : selectedPositiveWeight q x y τ ≠ 0) :
    SelectedActive q x y τ := by
  by_contra hn
  exact h (by simp only [selectedPositiveWeight,if_neg hn])

theorem scalar_sq_le_positive (q : Data α) (x : Frozen q) (hx : Function.Injective x)
    (y : Selected q) (hy : Function.Injective y) (τ : Character) (t : ℝ)
    (k : O) (χ : RayCharacter) :
    ‖selectedScalar q x y τ t k χ‖^2 ≤ selectedPositiveWeight q x y τ := by
  by_cases ha : SelectedActive q x y τ
  · rw [selectedPositiveWeight,if_pos ha]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (selected_scalar_norm q x hx y hy τ t k χ) 2
  · rw [scalar_zero_off_active q x y τ ha t k χ,selectedPositiveWeight,if_neg ha]
    norm_num

/-- The moving D character is retained BEFORE completing K to D^4 K.
The fixed-f twist, height, seed, punctures and ray all remain in commonVector. -/
def originalMovingCoefficient (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter)
    (v : keptResidual q) : ℂ :=
  commonVector q x seed τ t ξ v *
    (idealRowHom (primaryGenerator (selectedProduct q y)) (residualColumn q v.val))^2

/-- The actual residual polynomial at ORIGINAL k, with the D-natural-zero
mask still in its coefficients. There is no K4 completion in this definition. -/
def originalPolynomial (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter) (k : O) : ℂ :=
  gaussPolynomial Finset.univ
    (fun v : keptResidual q => primaryGenerator (residualColumn q v.val))
    (fun v => MixedSelectedCommon.primary_supported _ (kept_supported q v))
    (originalMovingCoefficient q x y seed τ t ξ) k

/-- Pointwise positive domination, suitable for the outer original-k sum
or integral. It retains character/gate zeros in the k-independent weight. -/
theorem original_ray_sq_le_positive (q : Data α) (x : Frozen q)
    (hx : Function.Injective x) (y : Selected q) (hy : Function.Injective y)
    (seed : Id) (τ : Character) (t : ℝ) (χ ξ : RayCharacter) (k : O) :
    ‖selectedScalar q x y τ t k χ * originalPolynomial q x y seed τ t ξ k‖^2 ≤
      selectedPositiveWeight q x y τ * ‖originalPolynomial q x y seed τ t ξ k‖^2 := by
  rw [norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (scalar_sq_le_positive q x hx y hy τ t k χ)
    (sq_nonneg _)

theorem moving_square_zero (D n : Id) (hD : Supported D) (hn : Supported n)
    (hc : ¬IsCoprime D n) : (idealRowHom (primaryGenerator D) n)^2 = 0 := by
  have hnc : ¬IsCoprime n D := fun h => hc h.symm
  have h6 := idealRowHom_sixth_mask (primaryGenerator D) n hn
  rw [idealRowHom_argument_pow _ 6 _ hn,primary_span_supported D hD,if_neg hnc] at h6
  rw [eq_zero_of_pow_eq_zero h6,zero_pow (by decide : 2 ≠ 0)]

theorem original_moving_zero_off_coprime (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter)
    (hD : Supported (selectedProduct q y)) (v : keptResidual q)
    (hc : ¬IsCoprime (selectedProduct q y) (residualColumn q v.val)) :
    originalMovingCoefficient q x y seed τ t ξ v = 0 := by
  rw [originalMovingCoefficient,moving_square_zero _ _ hD (kept_supported q v) hc,mul_zero]

/-- Exact zero completion: the selected-product mask stays INSIDE the
coefficient, and hence inside every subsequent squared source polynomial. -/
theorem original_moving_mask (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter)
    (hD : Supported (selectedProduct q y)) (v : keptResidual q) :
    originalMovingCoefficient q x y seed τ t ξ v =
      if IsCoprime (selectedProduct q y) (residualColumn q v.val) then
        originalMovingCoefficient q x y seed τ t ξ v else 0 := by
  by_cases hc : IsCoprime (selectedProduct q y) (residualColumn q v.val)
  · rw [if_pos hc]
  · rw [if_neg hc,original_moving_zero_off_coprime q x y seed τ t ξ hD v hc]

/-- An active original-frequency column carries both old/fresh coprimality
and the ORIGINAL character's natural zeros. No norm estimate supplies them. -/
theorem original_moving_active (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter)
    (hD : Supported (selectedProduct q y)) (v : keptResidual q)
    (hv : originalMovingCoefficient q x y seed τ t ξ v ≠ 0) :
    commonGate q.H q.R (frozenProduct q x) seed
      (restProduct q v.val.1) v.val.2.val.1 v.val.2.val.2 ∧
      idealCoeff τ (residualColumn q v.val) ≠ 0 ∧
      IsCoprime (frozenProduct q x * selectedProduct q y) (residualColumn q v.val) := by
  have hc : commonVector q x seed τ t ξ v ≠ 0 := left_ne_zero_of_mul hv
  have hb : baseCoefficient q x seed v.val ≠ 0 := by
    intro h
    exact hc (by simp only [commonVector,fixedCommonCoefficient,h,zero_mul])
  have hg : commonGate q.H q.R (frozenProduct q x) seed
      (restProduct q v.val.1) v.val.2.val.1 v.val.2.val.2 := by
    by_contra h
    exact hb (by simp only [baseCoefficient,MixedSupplierKernel.residualCoefficient,
      commonKernel,if_neg h,mul_zero])
  have hτ : idealCoeff τ (residualColumn q v.val) ≠ 0 := by
    intro h
    exact hc (by simp only [commonVector,fixedCommonCoefficient,heightCoeff,h,
      zero_mul,mul_zero])
  have hf : IsCoprime (frozenProduct q x) (residualColumn q v.val) :=
    common_gate_coprime q.H q.R (frozenProduct q x) seed
      (restProduct q v.val.1) v.val.2.val.1 v.val.2.val.2 hg
  have hdn : IsCoprime (selectedProduct q y) (residualColumn q v.val) := by
    by_contra h
    exact hv (original_moving_zero_off_coprime q x y seed τ t ξ hD v h)
  exact ⟨hg,hτ,hf.mul_left hdn⟩

/-- Both second common divisors C,E inherit coprimality with fD and with
the original fixed character. This is the local input to old+fresh forcing. -/
theorem original_common_divisor_active (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter)
    (hD : Supported (selectedProduct q y)) (v : keptResidual q)
    (hv : originalMovingCoefficient q x y seed τ t ξ v ≠ 0)
    (C : Id) (hC : C ∣ residualColumn q v.val) :
    IsCoprime (frozenProduct q x * selectedProduct q y) C ∧ IsCoprime τ.modulus C := by
  obtain ⟨_,hτ,hcop⟩ := original_moving_active q x y seed τ t ξ hD v hv
  have hτcop := ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff τ _).mp hτ).2.symm
  exact ⟨hcop.of_isCoprime_of_dvd_right hC,hτcop.of_isCoprime_of_dvd_right hC⟩

/-- Combined actual input: support of D is obtained from the scalar,
and the two coprimality facts are obtained from its actual common column. -/
theorem actual_outer_common_divisor (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (χ ξ : RayCharacter) (k : O)
    (hs : selectedScalar q x y τ t k χ ≠ 0) (v : keptResidual q)
    (hv : originalMovingCoefficient q x y seed τ t ξ v ≠ 0)
    (C : Id) (hC : C ∣ residualColumn q v.val) :
    SelectedActive q x y τ ∧
      IsCoprime (frozenProduct q x * selectedProduct q y) C ∧ IsCoprime τ.modulus C := by
  exact ⟨scalar_active q x y τ t k χ hs,
    original_common_divisor_active q x y seed τ t ξ
      (scalar_supported q x y τ t k χ hs).2 v hv C hC⟩

end
end Candidate.FourthPower.MixedSupplierOuterActive
