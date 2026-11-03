/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LargeSieve/CharacterBounds/FiniteSupportQuadraticForms.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleIdealRanges

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

private lemma support_guarded_subset (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (N : ℝ) {M : Type*} [Zero M] (g : Ideal (𝓞 F) → M) :
    Function.support (fun b : Ideal (𝓞 F) =>
      if Squarefree b ∧ b ⊔ c = ⊤ ∧ (Ideal.absNorm b : ℝ) ≤ N then g b else 0) ⊆
      (idealAdmissibleFinset F c N : Set (Ideal (𝓞 F))) := by
  intro b hb
  rw [Function.mem_support] at hb
  by_cases hcond : Squarefree b ∧ b ⊔ c = ⊤ ∧ (Ideal.absNorm b : ℝ) ≤ N
  · exact (mem_idealAdmissibleFinset F c N b).mpr hcond
  · rw [if_neg hcond] at hb
    exact absurd rfl hb

theorem finsum_character_eq_sum (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (𝓕 : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (N : ℝ) (lam : Ideal (𝓞 F) → ℂ) (a : Ideal (𝓞 F)) :
    (∑ᶠ b : Ideal (𝓞 F), (if Squarefree b ∧ b ⊔ c = ⊤ ∧
        (Ideal.absNorm b : ℝ) ≤ N then lam b * (𝓕.χ b) a else 0)) =
      ∑ b ∈ idealAdmissibleFinset F c N, lam b * (𝓕.χ b) a := by
  rw [finsum_eq_sum_of_support_subset (fun b : Ideal (𝓞 F) => (if Squarefree b ∧ b ⊔ c = ⊤ ∧
        (Ideal.absNorm b : ℝ) ≤ N then lam b * (𝓕.χ b) a else 0))
    (support_guarded_subset F c N (fun b => lam b * (𝓕.χ b) a))]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [if_pos ((mem_idealAdmissibleFinset F c N b).mp hb)]

theorem finsum_energy_eq_sum (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (𝓕 : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (M N : ℝ) (lam : Ideal (𝓞 F) → ℂ) :
    (∑ᶠ a : Ideal (𝓞 F), (if Squarefree a ∧ a ⊔ c = ⊤ ∧
        (Ideal.absNorm a : ℝ) ≤ M then
          ‖∑ᶠ b : Ideal (𝓞 F), (if Squarefree b ∧ b ⊔ c = ⊤ ∧
              (Ideal.absNorm b : ℝ) ≤ N then lam b * (𝓕.χ b) a else 0)‖ ^ 2
        else 0)) =
      ∑ a ∈ idealAdmissibleFinset F c M,
        ‖∑ b ∈ idealAdmissibleFinset F c N, lam b * (𝓕.χ b) a‖ ^ 2 := by
  have hfun : (fun a : Ideal (𝓞 F) => (if Squarefree a ∧ a ⊔ c = ⊤ ∧
        (Ideal.absNorm a : ℝ) ≤ M then
          ‖∑ᶠ b : Ideal (𝓞 F), (if Squarefree b ∧ b ⊔ c = ⊤ ∧
              (Ideal.absNorm b : ℝ) ≤ N then lam b * (𝓕.χ b) a else 0)‖ ^ 2
        else 0)) =
      fun a : Ideal (𝓞 F) => if Squarefree a ∧ a ⊔ c = ⊤ ∧
        (Ideal.absNorm a : ℝ) ≤ M then
          ‖∑ b ∈ idealAdmissibleFinset F c N, lam b * (𝓕.χ b) a‖ ^ 2 else 0 := by
    funext a
    rw [finsum_character_eq_sum F c 𝓕 N lam a]
  rw [hfun, finsum_eq_sum_of_support_subset _ (support_guarded_subset F c M
    (fun a => ‖∑ b ∈ idealAdmissibleFinset F c N, lam b * (𝓕.χ b) a‖ ^ 2))]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [if_pos ((mem_idealAdmissibleFinset F c M a).mp ha)]

theorem finsum_coeff_norm_sq_eq_sum (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (N : ℝ) (lam : Ideal (𝓞 F) → ℂ) :
    (∑ᶠ b : Ideal (𝓞 F), (if Squarefree b ∧ b ⊔ c = ⊤ ∧
        (Ideal.absNorm b : ℝ) ≤ N then ‖lam b‖ ^ 2 else 0)) =
      ∑ b ∈ idealAdmissibleFinset F c N, ‖lam b‖ ^ 2 := by
  rw [finsum_eq_sum_of_support_subset (fun b : Ideal (𝓞 F) => (if Squarefree b ∧ b ⊔ c = ⊤ ∧
        (Ideal.absNorm b : ℝ) ≤ N then ‖lam b‖ ^ 2 else 0))
    (support_guarded_subset F c N (fun b => ‖lam b‖ ^ 2))]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [if_pos ((mem_idealAdmissibleFinset F c N b).mp hb)]

end DedekindZetaZeroFree.LargeSieve.Sieve
