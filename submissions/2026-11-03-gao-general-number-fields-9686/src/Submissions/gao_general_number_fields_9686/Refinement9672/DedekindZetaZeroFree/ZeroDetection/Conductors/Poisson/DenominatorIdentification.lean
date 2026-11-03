/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/ZeroDetection/Conductors/Poisson/DenominatorIdentification.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyData
public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.DenominatorFamily

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.RawDenominatorPackage31

noncomputable section

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree NumberField
open _root_.DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison
open _root_.DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open _root_.DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
open _root_.DedekindZetaZeroFree.Quantitative.RawFixed
open DedekindZetaZeroFree.Quantitative.RawFixed
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem primMinus_eq_denominator (u : Frequency D.recipe) :
    FixedData.primMinus D u = (RawDenominatorFamily31.denominatorFamily D.recipe).omega u := by
  have h := (RawDenominatorFamily31.denominatorFamily D.recipe).raw_minus u
    (FixedData.rawFrequency D u) (FixedData.rawFrequency_u D u)
  exact MinusArithmetic.deleted_primitive_inducers_eq D.recipe.A
    (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u))
    (RawDenominatorExistence.rawDeletionSet_finite D.recipe (FixedData.rawFrequency D u))
    (RawDenominatorExistence.Sf_subset_rawDeletionSet D.recipe (FixedData.rawFrequency D u))
    _ _ (fun I => ((FixedData.pkg D).minus_mask u I).symm.trans (h I))

theorem primMinus_same (u : Frequency D.recipe) :
    Detector.samePrimitiveFrequencyCharacter F (FixedData.primMinus D u)
      ((RawDenominatorFamily31.denominatorFamily D.recipe).omega u) := by
  rw [primMinus_eq_denominator D u]
  intro n
  rfl

theorem primMinus_distinct (u v : Frequency D.recipe)
    (h : Detector.samePrimitiveFrequencyCharacter F (FixedData.primMinus D u)
      (FixedData.primMinus D v)) : u = v := by
  rw [primMinus_eq_denominator D u, primMinus_eq_denominator D v] at h
  exact (RawDenominatorFamily31.denominatorFamily D.recipe).distinct u v h

theorem primMinus_character_eq (u : Frequency D.recipe) (I : Ideal (𝓞 F)) :
    (FixedData.primMinus D u).character I =
      ((RawDenominatorFamily31.denominatorFamily D.recipe).omega u).character I := by
  rw [primMinus_eq_denominator D u]

theorem minus_conductor_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Frequency D.recipe,
      (Ideal.absNorm (FixedData.primMinus D u).conductor : ℝ) ≤
        c * frequencyNorm D.recipe u := by
  obtain ⟨c, hc, h⟩ := RawDenominatorFamily31.denominator_conductor_le D.recipe
  refine ⟨c, hc, fun u => ?_⟩
  rw [primMinus_eq_denominator D u]
  exact h u

theorem minus_local_tuples :
    ∃ L : Set (Detector.FixedSResidue.FullLocalCharacters D.recipe.A), L.Finite ∧
      (∀ σ ∈ L, Detector.FixedSResidue.HasFiniteOrder D.recipe.A σ) ∧
      ∀ u : Frequency D.recipe, ∃ σ ∈ L,
        Detector.HasFixedFullSLocalTuple F D.recipe.A (FixedData.primMinus D u) σ := by
  obtain ⟨L, hL, hord, hcov⟩ := RawDenominatorFamily31.denominator_local_tuples D.recipe
  refine ⟨L, hL, hord, fun u => ?_⟩
  rw [primMinus_eq_denominator D u]
  exact hcov u

theorem minus_conductor_sieve :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (U N : ℝ), 2 ≤ U → 2 ≤ N →
        ∀ (J : Finset (Frequency D.recipe)),
          (∀ u ∈ J, U ≤ frequencyNorm D.recipe u ∧ frequencyNorm D.recipe u < 2 * U) →
          ∀ (B : Finset (Ideal (𝓞 F))),
            (∀ I ∈ B, I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N) →
            ∀ b : Ideal (𝓞 F) → ℂ,
              (∑ u ∈ J, ‖∑ I ∈ B, b I * (FixedData.primMinus D u).character I‖ ^ 2) ≤
                C * (N + U ^ 2) * (N * U) ^ ε * ∑ I ∈ B, ‖b I‖ ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := RawDenominatorFamily31.raw_conductor_sieve D.recipe ε hε
  refine ⟨C, hC, fun U N hU hN J hJ B hB b => ?_⟩
  simp only [primMinus_character_eq D]
  exact h U N hU hN J hJ B hB b

theorem minus_conductor_sieve_finsum :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (U N : ℝ), 2 ≤ U → 2 ≤ N →
        ∀ (J : Finset (Frequency D.recipe)),
          (∀ u ∈ J, U ≤ frequencyNorm D.recipe u ∧ frequencyNorm D.recipe u < 2 * U) →
          ∀ b : Ideal (𝓞 F) → ℂ,
            (∀ I, b I ≠ 0 → I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N) →
              (∑ u ∈ J,
                ‖∑ᶠ I : Ideal (𝓞 F), b I * (FixedData.primMinus D u).character I‖ ^ 2) ≤
                C * (N + U ^ 2) * (N * U) ^ ε * ∑ᶠ I : Ideal (𝓞 F), ‖b I‖ ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := RawDenominatorFamily31.raw_conductor_sieve_finsum D.recipe ε hε
  refine ⟨C, hC, fun U N hU hN J hJ b hb => ?_⟩
  simp only [primMinus_character_eq D]
  exact h U N hU hN J hJ b hb

end

end DedekindZetaZeroFree.Quantitative.RawDenominatorPackage31

end Refinement9672
