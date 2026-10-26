/- Copyright (c) 2026 Sil. Apache-2.0.
The literal second-Poisson zero frequency on complete grouped ideals.
Reuse the baseline normalized correlation identity and primary generators.
Retain character zeros, bounded masks, the actual common divisor and the
external physical normalization. No second-diagonal bound is assumed.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedDivisorMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondDiagonal

set_option autoImplicit false
namespace Candidate.FourthPower.MixedSecondZero
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CenteredExceptionalCount CenteredMomentSecondDiagonal CompletedGauss
open SexticSieve ReferenceConvolution MixedDivisorMass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def generator (S : Finset Id) (I : S) : O := primaryGenerator I.val

theorem generator_span (S : Finset Id) (hs : ∀ I ∈ S, Supported I) (I : S) :
    Ideal.span {generator S I}=I.val :=
  (primaryGenerator_spec I.val (supported_primaryGenerator_ne_zero I.val (hs I.val I.property))).1

theorem generator_supported (S : Finset Id) (hs : ∀ I ∈ S, Supported I) (I : S) :
    Supported (Ideal.span {generator S I}) := by
  rw [generator_span S hs]
  exact hs I.val I.property

theorem generator_primary (S : Finset Id) (hs : ∀ I ∈ S, Supported I) (I : S) :
    goodLambda^2 ∣ generator S I-1 :=
  (primaryGenerator_spec I.val (supported_primaryGenerator_ne_zero I.val (hs I.val I.property))).2

theorem generator_injective (S : Finset Id) (hs : ∀ I ∈ S, Supported I) :
    Function.Injective (generator S) := by
  intro I J he
  apply Subtype.ext
  rw [← generator_span S hs I,← generator_span S hs J,he]

def energy (S : Finset Id) (hs : ∀ I ∈ S, Supported I) (c μ : Id → ℂ) : ℂ :=
  secondZeroEnergy Finset.univ (generator S) (generator_supported S hs)
    (fun I => c I.val*μ I.val)

theorem energy_mass (S : Finset Id) (hs : ∀ I ∈ S, Supported I) (c μ : Id → ℂ)
    (hμ : ∀ I ∈ S, ‖μ I‖ ≤ 1) : ‖energy S hs c μ‖ ≤ coefficientMass S c := by
  have hb := secondZeroEnergy_bound Finset.univ (generator S) (generator_supported S hs)
    (generator_primary S hs) (generator_injective S hs).injOn (fun I => c I.val*μ I.val)
  apply hb.trans
  calc
    _ ≤ ∑ I : S, ‖c I.val‖^2 := by
      apply Finset.sum_le_sum
      intro I _
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hμ I.val I.property)
    _ = _ := Finset.sum_coe_sort S (fun I : Id => ‖c I‖^2)

theorem normalized_energy_mass (S : Finset Id) (hs : ∀ I ∈ S, Supported I) (c μ : Id → ℂ)
    (hμ : ∀ I ∈ S, ‖μ I‖ ≤ 1) (κ : ℂ) (V : ℝ) (hV : 0 < V) :
    ‖(κ/(V:ℂ))*energy S hs c μ‖ ≤ (‖κ‖/V)*coefficientMass S c := by
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg hV.le]
  exact mul_le_mul_of_nonneg_left (energy_mass S hs c μ hμ) (div_nonneg (norm_nonneg _) hV.le)

theorem energy_zero_subunit (S : Finset Id) (hs : ∀ I ∈ S, Supported I) (c μ : Id → ℂ)
    (N : ℝ) (hN : N < 1)
    (hsize : ∀ I ∈ S, c I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ N) : energy S hs c μ=0 := by
  have hc (I : S) : c I.val=0 := by
    by_contra hn
    exact (not_le_of_gt hN) ((norm_one_le (hs I.val I.property).1).trans (hsize I.val I.property hn))
  simp only [energy,secondZeroEnergy,hc,zero_mul,Finset.sum_const_zero]

variable {ι : Type*} [Fintype ι]

theorem grouped_second_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (ι → Id)) (β : (ι → Id) → ℂ) (N B : ℝ),
      1 ≤ N → 0 ≤ B →
      (∀ v ∈ S, Supported (product v) ∧ (Ideal.absNorm (product v) : ℝ) ≤ N) →
      (∀ v ∈ S, ‖β v‖ ≤ B/Real.sqrt (Ideal.absNorm (product v) : ℝ)) →
      ∀ seed : Id, seed ≠ 0 → (∀ v ∈ S, β v ≠ 0 → seed ∣ product v) →
      ∀ (μ : Id → ℂ), (∀ I ∈ columns S, ‖μ I‖ ≤ 1) →
      ∀ hs : ∀ I ∈ columns S, Supported I,
      ‖energy (columns S) hs (coefficient S β) μ‖ ≤ C*N^ε*B^2/(Ideal.absNorm seed : ℝ) := by
  obtain ⟨C,hC,hb⟩ := grouped_divisor_mass (ι := ι) ε hε
  refine ⟨C,hC,?_⟩
  intro S β N B hN hB hgeom hβ seed hseed hdiv μ hμ hs
  exact (energy_mass (columns S) hs (coefficient S β) μ hμ).trans
    (hb S β N B hN hB hgeom hβ seed hseed hdiv)

theorem normalized_grouped_second_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (ι → Id)) (β : (ι → Id) → ℂ) (N B : ℝ),
      1 ≤ N → 0 ≤ B →
      (∀ v ∈ S, Supported (product v) ∧ (Ideal.absNorm (product v) : ℝ) ≤ N) →
      (∀ v ∈ S, ‖β v‖ ≤ B/Real.sqrt (Ideal.absNorm (product v) : ℝ)) →
      ∀ seed : Id, seed ≠ 0 → (∀ v ∈ S, β v ≠ 0 → seed ∣ product v) →
      ∀ (μ : Id → ℂ), (∀ I ∈ columns S, ‖μ I‖ ≤ 1) →
      ∀ (hs : ∀ I ∈ columns S, Supported I) (κ : ℂ) (V : ℝ), 0 < V →
      ‖(κ/(V:ℂ))*energy (columns S) hs (coefficient S β) μ‖ ≤
        C*‖κ‖*N^ε*B^2/(V*(Ideal.absNorm seed : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := grouped_second_zero (ι := ι) ε hε
  refine ⟨C,hC,?_⟩
  intro S β N B hN hB hgeom hβ seed hseed hdiv μ hμ hs κ V hV
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg hV.le]
  calc
    _ ≤ (‖κ‖/V)*(C*N^ε*B^2/(Ideal.absNorm seed : ℝ)) :=
      mul_le_mul_of_nonneg_left (hb S β N B hN hB hgeom hβ seed hseed hdiv μ hμ hs)
        (div_nonneg (norm_nonneg _) hV.le)
    _ = _ := by ring

end
end Candidate.FourthPower.MixedSecondZero
