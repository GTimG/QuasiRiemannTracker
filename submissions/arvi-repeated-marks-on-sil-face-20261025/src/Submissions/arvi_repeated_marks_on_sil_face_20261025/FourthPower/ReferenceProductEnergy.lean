/- Copyright (c) 2026 Sil. Apache-2.0.
Unconditional reference bound for products of the actual finite factors.
Every factor may carry a different fixed coefficient and mask, but all
variable rows use the same canonical character. No row energy is assumed.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.ReferenceConvolutionEnergy
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.ReferenceCoefficients

set_option autoImplicit false
namespace Candidate.FourthPower.ReferenceProductEnergy
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss
open ReferenceConvolution ReferenceConvolutionEnergy ReferenceCoefficients
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

/-- Same elementary supported-product argument as baseline
Descent/CanonicalChildSupport, without importing its unrelated descent chain. -/
theorem supported_product (v : α → Id) (hv : ∀ i, Supported (v i)) : Supported (product v) := by
  have hprod (T : Finset α) (ht : ∀ i ∈ T, Supported (v i)) : Supported (∏ i ∈ T, v i) := by
    induction T using Finset.induction_on with
    | empty =>
      change Supported (1 : Id)
      refine ⟨one_ne_zero,?_⟩
      intro P hP
      rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
      exact (Multiset.notMem_zero P hP).elim
    | @insert i T hi ih =>
      rw [Finset.prod_insert hi,supported_mul_iff]
      exact ⟨ht i (Finset.mem_insert_self _ _),ih (fun j hj => ht j (Finset.mem_insert_of_mem hj))⟩
  exact hprod Finset.univ (fun i _ => hv i)

theorem product_row_sum (pool : α → Finset Id) (a : α → Id → ℂ) (χ : Id →*₀ ℂ) :
    (∏ i, ∑ I ∈ pool i, a i I*χ I) =
      ∑ v ∈ Fintype.piFinset pool, (∏ i, a i (v i))*χ (product v) := by
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.prod_mul_distrib]
  simp only [product,map_prod]

/-- Uniform two-cap energy for any fixed number of full finite factors.
The pools include their fixed holes and natural coefficient masks. -/
theorem two_scale_product (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z R v y N T : ℝ),
      1 ≤ Z → 0 ≤ R → 1 ≤ N → 0 ≤ T →
      R+v ≤ L → v ≤ (4/5)*R → y ≤ R/2 → N ≤ Z^v → N ≤ Z^y*T →
      ∀ (rows : Finset O) (pool : α → Finset Id) (a : α → Id → ℂ) (H B : α → ℝ),
      (∀ i, 0 ≤ B i) → (∏ i, H i) ≤ N →
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ H i) →
      (∀ i I, I ∈ pool i → ‖a i I‖ ≤ B i/Real.sqrt (Ideal.absNorm I : ℝ)) →
      (∑ x ∈ rows, ‖∏ i, ∑ I ∈ pool i, a i I*idealRowHom x I‖^2) ≤
        C*Z^(R+ε)*(3+T^(1/3 : ℝ))*(∏ i, B i)^2 := by
  obtain ⟨C,hC,hb⟩ := two_scale_convolution (α:=α) ε L hε hL
  refine ⟨C,hC,?_⟩
  intro Z R v y N T hZ hR hN hT hcap hv hy hmax href rows pool a H B hB hHN hr hp ha
  have hmem (u : α → Id) (hu : u ∈ Fintype.piFinset pool) (i : α) : u i ∈ pool i :=
    Fintype.mem_piFinset.mp hu i
  have hs (u : α → Id) (hu : u ∈ Fintype.piFinset pool) :
      Supported (product u) ∧ (Ideal.absNorm (product u) : ℝ) ≤ N :=
    ⟨supported_product u (fun i => (hp i (u i) (hmem u hu i)).1),
      (product_length_bound u H (fun i => (hp i (u i) (hmem u hu i)).2)).trans hHN⟩
  have hβ (u : α → Id) (hu : u ∈ Fintype.piFinset pool) :
      ‖∏ i, a i (u i)‖ ≤ (∏ i, B i)/Real.sqrt (Ideal.absNorm (product u) : ℝ) :=
    product_coefficient_bound a B hB u (fun i => ha i (u i) (hmem u hu i))
  simp_rw [product_row_sum]
  exact hb Z R v y N T (∏ i, B i) hZ hR hN hT (Finset.prod_nonneg (fun i _ => hB i))
    hcap hv hy hmax href rows (Fintype.piFinset pool) (fun u => ∏ i, a i (u i)) hr hs hβ

end
end Candidate.FourthPower.ReferenceProductEnergy
