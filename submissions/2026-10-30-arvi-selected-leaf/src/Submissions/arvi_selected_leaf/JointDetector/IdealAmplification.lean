/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.InverseAmplification
import Submissions.arvi_selected_leaf.JointDetector.SelectedKernel

/-!
# Inverse amplification for ordinary ideal sources

The merged source set must contain every ideal product. All ideals, including
non-squarefree products and the unit ideal, retain the original `idealRowHom`
feature. Applications supply an amplifier response, coefficient square mass
and a product-fiber cardinality bound.
-/

namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentHeckeExpansion CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

/-- The entire ordinary product source family, without any projection. -/
def idealProductSources (sources monomials : Finset (Ideal O)) : Finset (Ideal O) :=
  (sources ×ˢ monomials).image fun p => p.1 * p.2

@[simp] theorem mem_idealProductSources (sources monomials : Finset (Ideal O))
    (T : Ideal O) :
    T ∈ idealProductSources sources monomials ↔
      ∃ I ∈ sources, ∃ J ∈ monomials, I * J = T := by
  simp only [idealProductSources, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨I, J⟩, ⟨hI, hJ⟩, h⟩
    exact ⟨I, hI, J, hJ, h⟩
  · rintro ⟨I, hI, J, hJ, h⟩
    exact ⟨(I, J), ⟨hI, hJ⟩, h⟩

/-- The canonical merged source family contains every product, including units. -/
theorem mul_mem_idealProductSources {sources monomials : Finset (Ideal O)}
    {I J : Ideal O} (hI : I ∈ sources) (hJ : J ∈ monomials) :
    I * J ∈ idealProductSources sources monomials :=
  (mem_idealProductSources sources monomials (I * J)).2 ⟨I, hI, J, hJ, rfl⟩

/-- The product as a map into any source set containing all the products. -/
def idealProductMerge (sources monomials merged : Finset (Ideal O))
    (hclosed : ∀ I ∈ sources, ∀ J ∈ monomials, I * J ∈ merged) :
    sources × monomials → merged :=
  fun p => ⟨p.1.val * p.2.val, hclosed _ p.1.property _ p.2.property⟩

@[simp] theorem idealProductMerge_val (sources monomials merged : Finset (Ideal O))
    (hclosed : ∀ I ∈ sources, ∀ J ∈ monomials, I * J ∈ merged)
    (p : sources × monomials) :
    (idealProductMerge sources monomials merged hclosed p).val = p.1.val * p.2.val := rfl

/-- Restricting a product fiber to finite subtype indices changes no count. -/
theorem idealProductMerge_fiber_card (sources monomials merged : Finset (Ideal O))
    (hclosed : ∀ I ∈ sources, ∀ J ∈ monomials, I * J ∈ merged) (T : merged) :
    (Finset.univ.filter fun p =>
      idealProductMerge sources monomials merged hclosed p = T).card =
    ((sources ×ˢ monomials).filter fun p => p.1 * p.2 = T.val).card := by
  classical
  apply Finset.card_bij (fun p _ => (p.1.val, p.2.val))
  · intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨p.1.property, p.2.property⟩, ?_⟩
    exact congrArg Subtype.val hp'
  · intro p hp q hq hpq
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hpq)
    · exact Subtype.ext (congrArg Prod.snd hpq)
  · intro p hp
    obtain ⟨hmem, hmul⟩ := Finset.mem_filter.mp hp
    obtain ⟨hI, hJ⟩ := Finset.mem_product.mp hmem
    refine ⟨(⟨p.1, hI⟩, ⟨p.2, hJ⟩), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact Subtype.ext hmul

/-- Exact specialization of finite inverse amplification to the actual
ordinary-ideal kernel. The response uses one common coefficient vector. -/
theorem selectedDualEnergy_inverse_amplification
    (rows : Finset O) (sources monomials merged : Finset (Ideal O))
    (hclosed : ∀ I ∈ sources, ∀ J ∈ monomials, I * J ∈ merged)
    (c : monomials → ℂ) (A C D : ℝ)
    (hA : 0 < A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hresponse : ∀ z : rows,
      A ≤ ‖∑ J : monomials, c J * idealRowHom z.val J.val‖ ^ 2)
    (hcoeff : ∑ J : monomials, ‖c J‖ ^ 2 ≤ C)
    (hfiber : ∀ T ∈ merged,
      (((sources ×ˢ monomials).filter fun p => p.1 * p.2 = T).card : ℝ) ≤ D)
    (coeff : rows → ℂ) :
    selectedDualEnergy rows sources coeff ≤
      C * D * selectedNorm rows merged / A * ∑ z, ‖coeff z‖ ^ 2 := by
  have hfiber' (T : merged) :
      ((Finset.univ.filter fun p =>
        idealProductMerge sources monomials merged hclosed p = T).card : ℝ) ≤ D := by
    rw [idealProductMerge_fiber_card]
    exact hfiber T.val T.property
  have htarget (b : rows → ℂ) :
      ∑ T : merged, ‖∑ z : rows, b z * idealRowHom z.val T.val‖ ^ 2 ≤
        selectedNorm rows merged * ∑ z, ‖b z‖ ^ 2 := by
    simpa only [selectedDualEnergy, selectedMatrix, mul_comm] using
      selectedDualEnergy_le rows merged b
  have h := inverse_amplification
    (idealProductMerge sources monomials merged hclosed)
    (fun (z : rows) (I : sources) => idealRowHom z.val I.val)
    (fun (z : rows) (J : monomials) => idealRowHom z.val J.val)
    (fun (z : rows) (T : merged) => idealRowHom z.val T.val) c A C D (selectedNorm rows merged)
    hA hC hD (show 0 ≤ selectedNorm rows merged from sq_nonneg _)
    (fun (z : rows) (I : sources) (J : monomials) => map_mul (idealRowHom z.val) I.val J.val)
    hresponse hcoeff hfiber' htarget coeff
  simpa only [selectedDualEnergy, selectedMatrix, mul_comm] using h

/-- The corresponding operator norm inequality, uniform in the dual vector. -/
theorem selectedNorm_inverse_amplification
    (rows : Finset O) (sources monomials merged : Finset (Ideal O))
    (hclosed : ∀ I ∈ sources, ∀ J ∈ monomials, I * J ∈ merged)
    (c : monomials → ℂ) (A C D : ℝ)
    (hA : 0 < A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hresponse : ∀ z : rows,
      A ≤ ‖∑ J : monomials, c J * idealRowHom z.val J.val‖ ^ 2)
    (hcoeff : ∑ J : monomials, ‖c J‖ ^ 2 ≤ C)
    (hfiber : ∀ T ∈ merged,
      (((sources ×ˢ monomials).filter fun p => p.1 * p.2 = T).card : ℝ) ≤ D) :
    selectedNorm rows sources ≤ C * D * selectedNorm rows merged / A := by
  apply selectedNorm_le_of_energy rows sources
    (C * D * selectedNorm rows merged / A)
  · exact div_nonneg (mul_nonneg (mul_nonneg hC hD) (sq_nonneg _)) hA.le
  · exact selectedDualEnergy_inverse_amplification rows sources monomials merged
      hclosed c A C D hA hC hD hresponse hcoeff hfiber

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.idealProductMerge_fiber_card
#print axioms Qrh.JointDetector.selectedNorm_inverse_amplification
