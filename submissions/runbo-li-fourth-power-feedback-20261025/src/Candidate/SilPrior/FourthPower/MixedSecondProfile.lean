/- Copyright (c) 2026 Sil. Apache-2.0.
The second-Poisson diagonal for bounded, unnormalized profile coefficients.
In particular no central half-power estimate is assumed for those profiles.
The physical denominator V and the genuine divisor seed are kept explicitly.
-/
import Candidate.SilPrior.FourthPower.MixedSecondZero

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.MixedSecondProfile
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve
open ReferenceConvolution MixedSecondZero
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem bounded_to_central (c : ℂ) (B N : ℝ) (hB : 0 ≤ B) (I : Id)
    (hI : I ≠ 0) (hN : (Ideal.absNorm I : ℝ) ≤ N) (hc : ‖c‖ ≤ B) :
    ‖c‖ ≤ (B*Real.sqrt N)/Real.sqrt (Ideal.absNorm I : ℝ) := by
  have hn : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  apply hc.trans
  exact (le_div_iff₀ (Real.sqrt_pos.mpr hn)).mpr
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hN) hB)

theorem bounded_second_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (ι → Id)) (β : (ι → Id) → ℂ) (N B : ℝ),
      1 ≤ N → 0 ≤ B →
      (∀ v ∈ S, Supported (product v) ∧ (Ideal.absNorm (product v) : ℝ) ≤ N) →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      ∀ seed : Id, seed ≠ 0 → (∀ v ∈ S, β v ≠ 0 → seed ∣ product v) →
      ∀ (μ : Id → ℂ), (∀ I ∈ columns S, ‖μ I‖ ≤ 1) →
      ∀ hs : ∀ I ∈ columns S, Supported I,
      ‖energy (columns S) hs (coefficient S β) μ‖ ≤
        C*B^2*N^(1+ε)/(Ideal.absNorm seed : ℝ) := by
  obtain ⟨C,hC,hb⟩ := grouped_second_zero (ι := ι) ε hε
  refine ⟨C,hC,?_⟩
  intro S β N B hN hB hgeom hβ seed hseed hdiv μ hμ hs
  have hn := zero_lt_one.trans_le hN
  have hh := hb S β N (B*Real.sqrt N) hN (mul_nonneg hB (Real.sqrt_nonneg _)) hgeom
    (fun v hv => bounded_to_central (β v) B N hB _ (hgeom v hv).1.1 (hgeom v hv).2 (hβ v hv))
    seed hseed hdiv μ hμ hs
  apply hh.trans_eq
  rw [mul_pow,Real.sq_sqrt hn.le,Real.rpow_add hn,Real.rpow_one]
  ring

theorem normalized_profile_second_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (ι → Id)) (β : (ι → Id) → ℂ) (L V B : ℝ),
      0 < L → 0 < V → 0 ≤ B →
      (∀ v ∈ S, Supported (product v) ∧ (Ideal.absNorm (product v) : ℝ) ≤ L*V) →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      ∀ seed : Id, seed ≠ 0 → (∀ v ∈ S, β v ≠ 0 → seed ∣ product v) →
      ∀ (μ : Id → ℂ), (∀ I ∈ columns S, ‖μ I‖ ≤ 1) →
      ∀ hs : ∀ I ∈ columns S, Supported I,
      (L*V < 1 → energy (columns S) hs (coefficient S β) μ=0) ∧
      ∀ κ : ℂ, ‖(κ/(V:ℂ))*energy (columns S) hs (coefficient S β) μ‖ ≤
        C*‖κ‖*B^2*L^(1+ε)*V^ε/(Ideal.absNorm seed : ℝ) := by
  obtain ⟨C,hC,hb⟩ := bounded_second_zero (ι := ι) ε hε
  refine ⟨C,hC,?_⟩
  intro S β L V B hL hV hB hgeom hβ seed hseed hdiv μ hμ hs
  have hz (hlow : L*V < 1) : energy (columns S) hs (coefficient S β) μ=0 := by
    apply energy_zero_subunit _ hs _ μ (L*V) hlow
    intro I hI _
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
    exact (hgeom v hv).2
  refine ⟨hz,?_⟩
  intro κ
  by_cases hlow : L*V < 1
  · rw [hz hlow,mul_zero,norm_zero]
    positivity
  have hh := hb S β (L*V) B (le_of_not_gt hlow) hB hgeom hβ seed hseed hdiv μ hμ hs
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg hV.le]
  apply (mul_le_mul_of_nonneg_left hh (div_nonneg (norm_nonneg _) hV.le)).trans_eq
  rw [Real.mul_rpow hL.le hV.le,Real.rpow_add hV,Real.rpow_one]
  field_simp

end
end Candidate.SilPrior.FourthPower.MixedSecondProfile
