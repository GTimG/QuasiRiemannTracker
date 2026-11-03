/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LFunctions/Hecke/RayCharacterEntireContinuation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterDescent
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LFunctions.Hecke.PartialRayZetaRegularization
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Analysis.FiniteCharacterPoleCancellation

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField

theorem rayCharacterEntire
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (χ : DedekindZetaZeroFree.RayClassCharacter K m)
    (hχ : ¬ χ.IsPrincipal) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ s : ℂ, 1 < s.re →
        HasSum (fun I : Ideal (𝓞 K) =>
          χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s) := by
  classical

  obtain ⟨ψ, hψdesc, hψprinc⟩ := rayCharacterDescent K m hm χ
  have hψ : ψ ≠ 1 := fun h => hχ (hψprinc.mpr h)

  obtain ⟨ρ, F, hF, hpartial⟩ := partialRayZetaRegularization K m hm
  haveI : Fintype (RayIdealClass K m hm) := Fintype.ofFinite _

  obtain ⟨f, hfdiff, hfsum⟩ := finiteCharacterEntireAssembly (rayIdealClass K m hm)
    (fun I s => (Ideal.absNorm I : ℂ) ^ (-s)) ψ hψ ρ F hF (fun c s hs =>
      (hpartial c s hs).congr_fun fun a => by
        by_cases hp : rayIdealClass K m hm a = some c <;> simp [hp])
  refine ⟨f, hfdiff, fun s hs => ?_⟩

  refine (hfsum s hs).congr_fun fun I => ?_
  rw [hψdesc I]
  cases hq : rayIdealClass K m hm I with
  | none => rfl
  | some c => rfl

end DedekindZetaZeroFree.AbelianQuotient
