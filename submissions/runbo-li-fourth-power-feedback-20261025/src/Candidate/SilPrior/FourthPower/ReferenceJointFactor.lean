/- Copyright (c) 2026 Sil. Apache-2.0.
A common joint restriction of the live marked tuple is a single actual
central factor. Injectivity and frozen-prime exclusions may stay in the
tuple set; no row-dependent coefficient vector is introduced.
-/
import Candidate.SilPrior.FourthPower.ReferenceFactors
import Candidate.SilPrior.FourthPower.ReferenceProductEnergy

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReferenceJointFactor
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ReferenceFactors ReferenceConvolution ReferenceCoefficients
local notation "Id" => Ideal HeckeFamily.O
variable {α : Type*} [Fintype α]

/-- The physical support length is N even when N is less than one. Only
the harmless divisor-multiplicity allowance uses max 1 N. -/
theorem grouped_factor (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (α → Id)) (β : (α → Id) → ℂ) (N B : ℝ),
      0 ≤ N → 0 ≤ B →
      (∀ v ∈ S, product v ≠ 0 ∧ (Ideal.absNorm (product v) : ℝ) ≤ N) →
      (∀ v ∈ S, ‖β v‖ ≤ B/Real.sqrt (Ideal.absNorm (product v) : ℝ)) →
      ∃ F : Factor, F.length = N ∧ F.amplitude = C*(max 1 N)^δ*B ∧
        ∀ χ : Character, F.value χ = ∑ v ∈ S, β v*idealCoeff χ (product v) := by
  obtain ⟨C,hC,hfiber⟩ := fiber_subpower (α:=α) δ hδ
  refine ⟨C,hC,?_⟩
  intro S β N B hN hB hs hβ
  have hlen (I) (hI : I ∈ columns S) : (Ideal.absNorm I : ℝ) ≤ N := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
    exact (hs v hv).2
  have hcoef (I) (hI : I ∈ columns S) :
      ‖coefficient S β I‖ ≤ (C*(max 1 N)^δ*B)/Real.sqrt (Ideal.absNorm I : ℝ) := by
    obtain ⟨v,hv,hvI⟩ := Finset.mem_image.mp hI
    have hI0 : I ≠ 0 := hvI ▸ (hs v hv).1
    have hsize : (Ideal.absNorm I : ℝ) ≤ max 1 N := (hlen I hI).trans (le_max_right _ _)
    apply (coefficient_norm S β B hB hβ I).trans
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hB
    exact (hfiber S I hI0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hsize hδ.le) hC.le)
  let F : Factor := {
    pool := columns S
    coefficient := coefficient S β
    length := N
    amplitude := C*(max 1 N)^δ*B
    length_nonneg := hN
    amplitude_nonneg := by positivity
    support_bound := hlen
    coefficient_bound := hcoef }
  refine ⟨F,rfl,rfl,?_⟩
  intro χ
  exact (row_identity S β (idealCoeff χ)).symm

/-- Any finite common restriction, including injectivity and holes depending
on the frozen assignment, preserves the actual whole marked product length.
The same resulting factor works for every physical character. -/
theorem joint_factor (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : α → Factor) (S : Finset (α → Id))
      (mask : (α → Id) → ℂ),
      (∀ v ∈ S, ∀ i, Supported (v i) ∧ v i ∈ (H i).pool) →
      (∀ v ∈ S, ‖mask v‖ ≤ 1) →
      ∃ F : Factor, F.length = ∏ i, (H i).length ∧
        F.amplitude = C*(max 1 (∏ i, (H i).length))^δ*(∏ i, (H i).amplitude) ∧
        ∀ χ : Character, F.value χ =
          ∑ v ∈ S, mask v*∏ i, (H i).coefficient (v i)*idealCoeff χ (v i) := by
  obtain ⟨C,hC,hgroup⟩ := grouped_factor (α:=α) δ hδ
  refine ⟨C,hC,?_⟩
  intro H S mask hs hm
  obtain ⟨F,hlen,hamp,hvalue⟩ := hgroup S (fun v => mask v*∏ i, (H i).coefficient (v i))
    (∏ i, (H i).length) (∏ i, (H i).amplitude)
    (Finset.prod_nonneg (fun i _ => (H i).length_nonneg))
    (Finset.prod_nonneg (fun i _ => (H i).amplitude_nonneg)) (by
      intro v hv
      exact ⟨(ReferenceProductEnergy.supported_product v (fun i => (hs v hv i).1)).1,
        product_length_bound v _ (fun i => (H i).support_bound _ (hs v hv i).2)⟩) (by
      intro v hv
      exact masked_product_bound (fun i => (H i).coefficient) (fun i => (H i).amplitude)
        (fun i => (H i).amplitude_nonneg) mask v (hm v hv)
        (fun i => (H i).coefficient_bound _ (hs v hv i).2))
  refine ⟨F,hlen,hamp,?_⟩
  intro χ
  rw [hvalue]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.prod_mul_distrib]
  simp only [product,map_prod,mul_assoc]

end
end Candidate.SilPrior.FourthPower.ReferenceJointFactor
