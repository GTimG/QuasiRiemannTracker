/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9672;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/HeckeCorollary.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Nonvanishing.Hecke.NonprincipalCharacter
public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Nonvanishing.Hecke.PrincipalCharacter

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree

open scoped NumberField

theorem heckeL_ne_zero
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (¬ χ.IsPrincipal → Differentiable ℂ f) ∧
      (∀ s, 1 < s.re → HasSum (fun I : Ideal (𝓞 K) =>
        χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
      ∀ s, 1209 / 1250 < s.re → (s ≠ 1 ∨ ¬ χ.IsPrincipal) → f s ≠ 0 := by
  by_cases hχ : χ.IsPrincipal
  · obtain ⟨f, hf, hsum, hnz⟩ := HeckeCorollary.principalRayCharacter_ne_zero K m hm χ hχ
    refine ⟨f, hf, fun h => (h hχ).elim, hsum, ?_⟩
    intro s hs hregular
    exact hnz s hs (hregular.resolve_right (not_not.mpr hχ))
  · obtain ⟨f, hf, hsum, hnz⟩ := HeckeCorollary.nonprincipalRayCharacter_ne_zero K m hm χ hχ
    exact ⟨f, hf.differentiableOn, fun _ => hf, hsum, fun s hs _ => hnz s hs⟩

end DedekindZetaZeroFree

end Refinement9672
