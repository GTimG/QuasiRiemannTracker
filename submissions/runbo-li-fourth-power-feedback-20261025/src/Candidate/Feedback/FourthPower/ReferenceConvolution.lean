/- Copyright (c) 2026 Sil. Apache-2.0.
Whole common-column convolution, with arbitrary fixed tuple restrictions.
Its multiplicity is bounded by the pinned baseline ideal divisor estimate.
The row character is applied only after the common coefficients are formed.
-/
import Candidate.Feedback.FourthPower.SieveCentralReference

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.ReferenceConvolution
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss IdealMobiusDivisorSum
open SieveReference SieveElementReference SieveCentralReference
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

def product (v : α → Id) : Id := ∏ i, v i
def fiber (S : Finset (α → Id)) (I : Id) : Finset (α → Id) :=
  S.filter (fun v => product v = I)
def columns (S : Finset (α → Id)) : Finset Id := S.image product
def coefficient (S : Finset (α → Id)) (β : (α → Id) → ℂ) (I : Id) : ℂ :=
  ∑ v ∈ fiber S I, β v

theorem fiber_card (S : Finset (α → Id)) (I : Id) (hI : I ≠ 0) :
    (fiber S I).card ≤ (idealDivisors I).card ^ Fintype.card α := by
  have hs : fiber S I ⊆ Fintype.piFinset (fun _ : α => idealDivisors I) := by
    intro v hv
    simp only [Fintype.mem_piFinset]
    intro i
    apply (mem_idealDivisors hI).mpr
    rw [← (Finset.mem_filter.mp hv).2]
    exact Finset.dvd_prod_of_mem v (Finset.mem_univ i)
  simpa only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]
    using Finset.card_le_card hs

theorem fiber_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (α → Id)) (I : Id), I ≠ 0 →
      ((fiber S I).card : ℝ) ≤ C*(Ideal.absNorm I : ℝ)^δ := by
  let r : ℕ := Fintype.card α
  obtain ⟨D,hD,hb⟩ := IdealDivisorBound.ideal_divisor_small_power
    (δ/((r : ℝ)+1)) (by positivity)
  refine ⟨D^r,pow_pos hD _,?_⟩
  intro S I hI
  have hN : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hexp : (δ/((r : ℝ)+1))*(r : ℝ) ≤ δ := by
    have he : (δ/((r : ℝ)+1))*((r : ℝ)+1) = δ := div_mul_cancel₀ _ (by positivity)
    have hp : 0 < δ/((r : ℝ)+1) := by positivity
    nlinarith
  calc
    _ ≤ ((idealDivisors I).card : ℝ)^r := by exact_mod_cast fiber_card S I hI
    _ ≤ (D*(Ideal.absNorm I : ℝ)^(δ/((r : ℝ)+1)))^r :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hb I hI) _
    _ = D^r*(Ideal.absNorm I : ℝ)^((δ/((r : ℝ)+1))*(r : ℝ)) := by
      rw [mul_pow,← Real.rpow_natCast ((Ideal.absNorm I : ℝ)^(δ/((r : ℝ)+1))) r,
        ← Real.rpow_mul (zero_le_one.trans hN)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN hexp) (pow_nonneg hD.le _)

theorem row_identity (S : Finset (α → Id)) (β : (α → Id) → ℂ) (χ : Id → ℂ) :
    (∑ v ∈ S, β v*χ (product v)) =
      ∑ I ∈ columns S, coefficient S β I*χ I := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩ : ∀ v ∈ S, product v ∈ columns S)
    (fun v => β v*χ (product v))]
  apply Finset.sum_congr rfl
  intro I _
  rw [coefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [(Finset.mem_filter.mp hv).2]

theorem multiplicative_row_identity (S : Finset (α → Id)) (a : α → Id → ℂ)
    (χ : Id →*₀ ℂ) :
    (∑ v ∈ S, ∏ i, a i (v i)*χ (v i)) =
      ∑ I ∈ columns S, coefficient S (fun v => ∏ i, a i (v i)) I*χ I := by
  simp only [Finset.prod_mul_distrib,← map_prod]
  exact row_identity S (fun v => ∏ i, a i (v i)) χ

theorem coefficient_norm (S : Finset (α → Id)) (β : (α → Id) → ℂ)
    (B : ℝ) (_hB : 0 ≤ B)
    (hb : ∀ v ∈ S, ‖β v‖ ≤ B / Real.sqrt (Ideal.absNorm (product v) : ℝ)) (I : Id) :
    ‖coefficient S β I‖ ≤ ((fiber S I).card : ℝ)*B/Real.sqrt (Ideal.absNorm I : ℝ) := by
  unfold coefficient
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _v ∈ fiber S I, B/Real.sqrt (Ideal.absNorm I : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      have hh := hb v (Finset.mem_filter.mp hv).1
      simpa only [(Finset.mem_filter.mp hv).2] using hh
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- Pointwise central envelope of the literal grouped coefficient. All
constants precede the tuple set and vector; no row enters the coefficient. -/
theorem central_envelope (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (α → Id)) (β : (α → Id) → ℂ) (N B : ℝ),
      1 ≤ N → 0 ≤ B →
      (∀ v ∈ S, product v ≠ 0 ∧ (Ideal.absNorm (product v) : ℝ) ≤ N) →
      (∀ v ∈ S, ‖β v‖ ≤ B/Real.sqrt (Ideal.absNorm (product v) : ℝ)) →
      ∀ I ∈ columns S, ‖coefficient S β I‖^2 ≤ (C*N^ε*B^2)/(Ideal.absNorm I : ℝ) := by
  obtain ⟨C,hC,hb⟩ := fiber_subpower (α:=α) (ε/2) (by positivity)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro S β N B hN hB hs hβ I hI
  obtain ⟨v,hv,hvI⟩ := Finset.mem_image.mp hI
  have hI0 : I ≠ 0 := hvI ▸ (hs v hv).1
  have hIN : (Ideal.absNorm I : ℝ) ≤ N := hvI ▸ (hs v hv).2
  have hn : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
  have hnrm : ‖coefficient S β I‖ ≤ C*N^(ε/2)*B/Real.sqrt (Ideal.absNorm I : ℝ) := by
    apply (coefficient_norm S β B hB hβ I).trans
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hB
    exact (hb S I hI0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hn.le hIN (by positivity : 0 ≤ ε/2)) hC.le)
  have hp : (N^(ε/2))^2 = N^ε := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (zero_le_one.trans hN)]
    congr 1
    ring
  have hh := pow_le_pow_left₀ (norm_nonneg _) hnrm 2
  simpa only [div_pow,mul_pow,hp,Real.sq_sqrt hn.le] using hh

end
end Candidate.Feedback.FourthPower.ReferenceConvolution
