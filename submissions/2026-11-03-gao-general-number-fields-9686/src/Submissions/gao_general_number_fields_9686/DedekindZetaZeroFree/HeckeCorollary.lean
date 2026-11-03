/-
2026-11-03 refinement by Zhongpai Gao (https://github.com/Gaozhongpai).
The following header records the PR #114 source provenance at 09afbb4ce6570c1615d58509dc197fc9f0956b7d.
This file now contains the native parameter refinement at
829193272c1eaf223bb7228fbfb9003f414808e9; local imports are relocated under Submissions.gao_general_number_fields_9686.
Original declaration namespaces and all source attribution are retained.
Native compilation and tracker admission remain pending; see Candidate.Provenance.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HeckeCorollary.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Nonvanishing.Hecke.NonprincipalCharacter
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Nonvanishing.Hecke.PrincipalCharacter

@[expose] public section

namespace DedekindZetaZeroFree

open scoped NumberField

theorem heckeL_ne_zero
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (¬ χ.IsPrincipal → Differentiable ℂ f) ∧
      (∀ s, 1 < s.re → HasSum (fun I : Ideal (𝓞 K) =>
        χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
      ∀ s, 4843 / 5000 < s.re → (s ≠ 1 ∨ ¬ χ.IsPrincipal) → f s ≠ 0 := by
  by_cases hχ : χ.IsPrincipal
  · obtain ⟨f, hf, hsum, hnz⟩ := HeckeCorollary.principalRayCharacter_ne_zero K m hm χ hχ
    refine ⟨f, hf, fun h => (h hχ).elim, hsum, ?_⟩
    intro s hs hregular
    exact hnz s hs (hregular.resolve_right (not_not.mpr hχ))
  · obtain ⟨f, hf, hsum, hnz⟩ := HeckeCorollary.nonprincipalRayCharacter_ne_zero K m hm χ hχ
    exact ⟨f, hf.differentiableOn, fun _ => hf, hsum, fun s hs _ => hnz s hs⟩

end DedekindZetaZeroFree
