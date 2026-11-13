/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/GlobalClassFieldTheory/MaximalAbelianGlobalArtin.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.GlobalClassFieldTheory.IsMaximalAbelianGlobalArtin
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Theorems.GlobalClassFieldTheory.TopologicalGlobalReciprocity

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The maximal abelian global Artin map

This map from Mathlib's idèle class group to Mathlib's abelianized absolute
Galois group is continuous, surjective, and has the identity component as
its kernel. It is induced by a topological reciprocity isomorphism. The
statement does not yet fix Frobenius normalization at finite levels, so it
does not assert uniqueness of the map.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

/-- A continuous surjective global Artin map with the expected kernel exists. -/
theorem maximalAbelianGlobalArtin
    (K : Type u) [Field K] [NumberField K] :
    ∃ artin : NumberField.IdeleClassGroup (𝓞 K) K →ₜ*
        Field.absoluteGaloisGroupAbelianization K,
      IsMaximalAbelianGlobalArtin K artin := by
  obtain ⟨e⟩ := topologicalGlobalReciprocity K
  let H : Subgroup (NumberField.IdeleClassGroup (𝓞 K) K) :=
    Subgroup.connectedComponentOfOne _
  let q : NumberField.IdeleClassGroup (𝓞 K) K →ₜ*
      IdeleClassConnectedQuotient K :=
    { toMonoidHom := QuotientGroup.mk' H
      continuous_toFun := QuotientGroup.continuous_mk }
  let artin : NumberField.IdeleClassGroup (𝓞 K) K →ₜ*
      Field.absoluteGaloisGroupAbelianization K :=
    (ContinuousMonoidHom.toContinuousMonoidHom e).comp q
  refine ⟨artin, ?_, ?_⟩
  · intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H y
    exact ⟨x, rfl⟩
  · change artin.toMonoidHom.ker = H
    change (e.toMonoidHom.comp (QuotientGroup.mk' H)).ker = H
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' H) e.toMonoidHom
      e.injective]
    exact QuotientGroup.ker_mk' H

end ClassFieldTheory

end
