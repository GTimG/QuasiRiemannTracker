/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Conductors/PrimitiveTrivialCharacter.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMu12Pointwise

open scoped NumberField

theorem principal_primitive_top_character_exists
    (F : Type) [Field F] [NumberField F] :
    ∃ η : RayClassCharacter F ⊤, η.IsPrincipal ∧ η.IsPrimitive := by
  refine ⟨{ toFun := fun I => if I = ⊥ then 0 else 1
            map_mul' := ?_
            map_top' := ?_
            eq_zero_iff' := ?_
            map_span' := ?_ }, ?_, ?_⟩
  · intro I J
    by_cases hI : I = ⊥
    · simp [hI]
    by_cases hJ : J = ⊥
    · simp [hJ]
    simp [hI, hJ, Ideal.mul_eq_bot]
  · simp
  · intro I
    simp
  · intro α hα _ _
    simp [Ideal.span_singleton_eq_bot, hα]
  · intro I hI _
    simp [hI]
  · intro 𝔣 h𝔣
    exact absurd h𝔣 (not_lt_of_ge le_top)

end DedekindZetaZeroFree.PrincipalMu12Pointwise
