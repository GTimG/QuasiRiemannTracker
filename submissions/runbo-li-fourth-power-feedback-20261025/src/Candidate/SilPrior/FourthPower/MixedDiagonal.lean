/- Copyright (c) 2026 Sil. Apache-2.0.
The coefficient diagonal keeps the whole ordinary-plus-marked ideal.
Fifth-free columns have no distinct sixth-power-equivalent partners.
The actual grouped convolution has subpower square mass, uniformly over
all common tuple restrictions; marked prime factors are never omitted.
-/
import Candidate.SilPrior.FourthPower.ReferenceConvolution
import Candidate.SilPrior.FourthPower.KernelWholeColumns

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.MixedDiagonal
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredExceptionalCount UniqueFactorizationMonoid EisensteinSchwartzPoisson ConcreteTraceCRT
open QuadraticInitialBound SexticSieve ReferenceConvolution SieveDescent SieveCentralReference
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem sixth_free_of_fifth {I : Id} (hI : PowerFree 5 I) : PowerFree 6 I :=
  fun P hp hd => hI P hp ((pow_dvd_pow P (by decide : 5 ≤ 6)).trans hd)

theorem remainder_eq (I : Id) (hI : Supported I) (hf : PowerFree 6 I) :
    sixthRemainder I=I := by
  apply ideal_eq_of_valuation_eq (sixthRemainder_ne_zero I) hI.1
  intro P
  rw [sixthRemainder_valuation]
  apply Nat.mod_eq_of_lt
  by_cases hP : P ∈ normalizedFactors I
  · exact SievePrimitive.exponent_lt I hI hf ⟨P,Multiset.mem_toFinset.mpr hP⟩
  · have hz : valuation I P=0 := Multiset.count_eq_zero.mpr hP
    rw [hz]
    decide

theorem fifth_free_diagonal (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 5 I) (hfJ : PowerFree 5 J) :
    (∀ P : Id, valuation I P % 6=valuation J P % 6) ↔ I=J := by
  rw [← sixthRemainder_eq_iff,remainder_eq I hI (sixth_free_of_fifth hfI),
    remainder_eq J hJ (sixth_free_of_fifth hfJ)]

variable {ι : Type*} [Fintype ι]

/-- This is the square mass after grouping equal whole ideals, so it pays
all tuple collisions by the proved divisor bound. It is not the easier
ungrouped tuple mass. -/
theorem grouped_mass (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (ι → Id)) (β : (ι → Id) → ℂ) (N B : ℝ),
      1 ≤ N → 0 ≤ B →
      (∀ v ∈ S, Supported (product v) ∧ (Ideal.absNorm (product v) : ℝ) ≤ N) →
      (∀ v ∈ S, ‖β v‖ ≤ B/Real.sqrt (Ideal.absNorm (product v) : ℝ)) →
      coefficientMass (columns S) (coefficient S β) ≤ C*N^ε*B^2 := by
  obtain ⟨C,hC,hb⟩ := central_envelope (α := ι) (ε/2) (half_pos hε)
  let K := rootMass (1+ε/2)+1
  have hK : 0 < K := lt_add_of_le_of_pos (rootMass_nonneg _) zero_lt_one
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro S β N B hN hB hs hβ
  have hcols (I : Id) (hi : I ∈ columns S) :
      Supported I ∧ (Ideal.absNorm I : ℝ) ≤ N := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
    exact hs v hv
  have hm := reciprocal_mass (ε/2) (half_pos hε) N (zero_lt_one.trans_le hN) (columns S) hcols
  have he := hb S β N B hN hB (fun v hv => ⟨(hs v hv).1.1,(hs v hv).2⟩) hβ
  calc
    _ ≤ ∑ I ∈ columns S, (C*N^(ε/2)*B^2)/(Ideal.absNorm I : ℝ) := Finset.sum_le_sum he
    _ = (C*N^(ε/2)*B^2)*(∑ I ∈ columns S, (Ideal.absNorm I : ℝ)⁻¹) := by
      simp only [div_eq_mul_inv,Finset.mul_sum]
    _ ≤ (C*N^(ε/2)*B^2)*(N^(ε/2)*rootMass (1+ε/2)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ (C*N^(ε/2)*B^2)*(N^(ε/2)*K) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)) (by positivity)) (by positivity)
    _ = (C*K)*(N^(ε/2)*N^(ε/2))*B^2 := by ring
    _ = _ := by rw [← Real.rpow_add (zero_lt_one.trans_le hN),show ε/2+ε/2=ε by ring]

theorem masked_diagonal (I : Id) (μ : O → ℂ) (hμ : ∀ z, ‖μ z‖ ≤ 1)
    (W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, μ z*(star (idealRowHom z I)*idealRowHom z I)*W (‖eisEmbedding z‖^2/M)‖ ≤
      diagonalControl W*M := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖^2/M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM0)
  have hb (z : O) :
      ‖μ z*(star (idealRowHom z I)*idealRowHom z I)*W (‖eisEmbedding z‖^2/M)‖ ≤
        ‖W (‖eisEmbedding z‖^2/M)‖ := by
    rw [norm_mul,norm_mul,norm_mul,norm_star]
    have hi : ‖idealRowHom z I‖*‖idealRowHom z I‖ ≤ 1 := by
      simpa only [one_mul] using mul_le_mul (idealRowHom_norm z I) (idealRowHom_norm z I)
        (norm_nonneg _) zero_le_one
    have hh : ‖μ z‖*(‖idealRowHom z I‖*‖idealRowHom z I‖) ≤ 1 := by
      simpa only [one_mul] using mul_le_mul (hμ z) hi (by positivity) zero_le_one
    exact mul_le_of_le_one_left (norm_nonneg _) hh
  have ht := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs
  exact (norm_tsum_le_tsum_norm ht).trans
    ((ht.tsum_le_tsum hb hs).trans (radial_weight_lattice_bound W M hM))

theorem grouped_smooth_diagonal (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (ι → Id)) (β : (ι → Id) → ℂ) (N B : ℝ),
      1 ≤ N → 0 ≤ B →
      (∀ v ∈ S, Supported (product v) ∧ (Ideal.absNorm (product v) : ℝ) ≤ N) →
      (∀ v ∈ S, ‖β v‖ ≤ B/Real.sqrt (Ideal.absNorm (product v) : ℝ)) →
      ∀ (μ : O → ℂ), (∀ z, ‖μ z‖ ≤ 1) → ∀ (W : 𝓢(ℝ,ℂ)) (M : ℝ), 1 ≤ M →
      (∑ I ∈ columns S, ‖coefficient S β I‖^2*
        ‖∑' z : O, μ z*(star (idealRowHom z I)*idealRowHom z I)*W (‖eisEmbedding z‖^2/M)‖) ≤
          C*N^ε*B^2*(diagonalControl W*M) := by
  obtain ⟨C,hC,hb⟩ := grouped_mass (ι := ι) ε hε
  refine ⟨C,hC,?_⟩
  intro S β N B hN hB hs hβ μ hμ W M hM
  calc
    _ ≤ ∑ I ∈ columns S, ‖coefficient S β I‖^2*(diagonalControl W*M) :=
      Finset.sum_le_sum (fun I _ => mul_le_mul_of_nonneg_left
        (masked_diagonal I μ hμ W M hM) (sq_nonneg _))
    _ = coefficientMass (columns S) (coefficient S β)*(diagonalControl W*M) :=
      (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hb S β N B hN hB hs hβ)
      (mul_nonneg (diagonalControl_nonneg W) (zero_le_one.trans hM))

end
end Candidate.SilPrior.FourthPower.MixedDiagonal
