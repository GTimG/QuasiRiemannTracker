/- Copyright (c) 2026 Sil. Apache-2.0.
Grouped central square mass with the actual common-divisor saving.
Only nonzero tuple coefficients need carry the divisor. The divisor is
removed by an injective ideal quotient, not by dropping its norm cost.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedDiagonal

set_option autoImplicit false
namespace Candidate.FourthPower.MixedDivisorMass
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve CenteredExceptionalCount
open SexticSieve ReferenceConvolution SieveDescent SieveCentralReference
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem reciprocal_divisor_mass (δ N : ℝ) (hδ : 0 < δ) (hN : 0 < N)
    (S : Finset Id) (hS : ∀ I ∈ S, Supported I ∧ (Ideal.absNorm I : ℝ) ≤ N)
    (seed : Id) (hseed : seed ≠ 0) (hdiv : ∀ I ∈ S, seed ∣ I) :
    (∑ I ∈ S, (Ideal.absNorm I : ℝ)⁻¹) ≤ N^δ*rootMass (1+δ)/(Ideal.absNorm seed : ℝ) := by
  let Q := S.image (idealQuotient seed)
  have hQ (J : Id) (hJ : J ∈ Q) : Supported J ∧ (Ideal.absNorm J : ℝ) ≤ N := by
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    have hd := idealQuotient_dvd (hdiv I hI)
    exact ⟨SixthDecomposition.supported_dvd (hS I hI).1 hd,
      (norm_le_of_dvd (hS I hI).1.1 hd).trans (hS I hI).2⟩
  have hb := reciprocal_mass δ hδ N hN Q hQ
  have hinj : Set.InjOn (idealQuotient seed) S := fun I hI J hJ he =>
    idealQuotient_injective_on seed (hdiv I hI) (hdiv J hJ) he
  rw [show Q=S.image (idealQuotient seed) from rfl,Finset.sum_image hinj] at hb
  have he (I : Id) (hI : I ∈ S) : (Ideal.absNorm I : ℝ)⁻¹ =
      (Ideal.absNorm seed : ℝ)⁻¹*(Ideal.absNorm (idealQuotient seed I) : ℝ)⁻¹ := by
    have hn : (Ideal.absNorm seed : ℝ)*(Ideal.absNorm (idealQuotient seed I) : ℝ) =
        (Ideal.absNorm I : ℝ) := by
      rw [← Nat.cast_mul,← map_mul,idealQuotient_mul (hdiv I hI)]
    rw [← hn,mul_inv_rev,mul_comm]
  calc
    _ = (Ideal.absNorm seed : ℝ)⁻¹ * ∑ I ∈ S, (Ideal.absNorm (idealQuotient seed I) : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl he
    _ ≤ (Ideal.absNorm seed : ℝ)⁻¹*(N^δ*rootMass (1+δ)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_pos hseed).le)
    _ = _ := by ring

variable {ι : Type*} [Fintype ι]

theorem coefficient_zero_of_not_dvd (S : Finset (ι → Id)) (β : (ι → Id) → ℂ)
    (seed I : Id) (hdiv : ∀ v ∈ S, β v ≠ 0 → seed ∣ product v) (hn : ¬seed ∣ I) :
    coefficient S β I=0 := by
  apply Finset.sum_eq_zero
  intro v hv
  by_contra hv0
  exact hn ((Finset.mem_filter.mp hv).2 ▸ hdiv v (Finset.mem_filter.mp hv).1 hv0)

/-- Nonzero coefficients retain their real common divisor after grouping.
The constant is independent of that divisor and of all coefficient masks. -/
theorem grouped_divisor_mass (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (ι → Id)) (β : (ι → Id) → ℂ) (N B : ℝ),
      1 ≤ N → 0 ≤ B →
      (∀ v ∈ S, Supported (product v) ∧ (Ideal.absNorm (product v) : ℝ) ≤ N) →
      (∀ v ∈ S, ‖β v‖ ≤ B/Real.sqrt (Ideal.absNorm (product v) : ℝ)) →
      ∀ seed : Id, seed ≠ 0 → (∀ v ∈ S, β v ≠ 0 → seed ∣ product v) →
      coefficientMass (columns S) (coefficient S β) ≤ C*N^ε*B^2/(Ideal.absNorm seed : ℝ) := by
  obtain ⟨C,hC,hb⟩ := central_envelope (α := ι) (ε/2) (half_pos hε)
  let K := rootMass (1+ε/2)+1
  have hK : 0 < K := lt_add_of_le_of_pos (rootMass_nonneg _) zero_lt_one
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro S β N B hN hB hs hβ seed hseed hdiv
  let F := (columns S).filter (fun I => seed ∣ I)
  have hF (I : Id) (hi : I ∈ F) : Supported I ∧ (Ideal.absNorm I : ℝ) ≤ N := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hi).1
    exact hs v hv
  have hFsub : F ⊆ columns S := Finset.filter_subset _ _
  have hsum : coefficientMass (columns S) (coefficient S β) =
      ∑ I ∈ F, ‖coefficient S β I‖^2 := by
    symm
    apply Finset.sum_subset hFsub
    intro I hI hn
    have hnd : ¬seed ∣ I := fun hd => hn (Finset.mem_filter.mpr ⟨hI,hd⟩)
    rw [coefficient_zero_of_not_dvd S β seed I hdiv hnd,norm_zero,zero_pow (by decide : 2 ≠ 0)]
  have hm := reciprocal_divisor_mass (ε/2) N (half_pos hε) (zero_lt_one.trans_le hN)
    F hF seed hseed (fun I hi => (Finset.mem_filter.mp hi).2)
  have he := hb S β N B hN hB (fun v hv => ⟨(hs v hv).1.1,(hs v hv).2⟩) hβ
  have hn : 0 < (Ideal.absNorm seed : ℝ) := norm_pos hseed
  rw [hsum]
  calc
    _ ≤ ∑ I ∈ F, (C*N^(ε/2)*B^2)/(Ideal.absNorm I : ℝ) :=
      Finset.sum_le_sum (fun I hi => he I (hFsub hi))
    _ = (C*N^(ε/2)*B^2)*(∑ I ∈ F, (Ideal.absNorm I : ℝ)⁻¹) := by
      simp only [div_eq_mul_inv,Finset.mul_sum]
    _ ≤ (C*N^(ε/2)*B^2)*(N^(ε/2)*rootMass (1+ε/2)/(Ideal.absNorm seed : ℝ)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ (C*N^(ε/2)*B^2)*(N^(ε/2)*K/(Ideal.absNorm seed : ℝ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)) (by positivity)) hn.le)
        (by positivity)
    _ = ((C*K)*(N^(ε/2)*N^(ε/2))*B^2)/(Ideal.absNorm seed : ℝ) := by ring
    _ = _ := by rw [← Real.rpow_add (zero_lt_one.trans_le hN),show ε/2+ε/2=ε by ring]

end
end Candidate.FourthPower.MixedDivisorMass
