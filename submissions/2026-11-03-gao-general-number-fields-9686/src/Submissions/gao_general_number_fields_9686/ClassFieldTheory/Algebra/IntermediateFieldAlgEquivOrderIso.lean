/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Algebra/IntermediateFieldAlgEquivOrderIso.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Intermediate fields under an algebra equivalence

An algebra equivalence of ambient fields induces an order equivalence of
their intermediate-field lattices.  This is the ambient-change step used for
Mathlib's chosen separable closures.
-/

noncomputable section

namespace ClassFieldTheory

universe u v w

variable {F : Type u} {L : Type v} {L' : Type w}
  [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']

/-- Map intermediate fields along an algebra equivalence of ambient fields. -/
def intermediateFieldAlgEquivOrderIso (e : L ≃ₐ[F] L') :
    IntermediateField F L ≃o IntermediateField F L' where
  toEquiv := {
    toFun := fun E => E.map e.toAlgHom
    invFun := fun E => E.map e.symm.toAlgHom
    left_inv := by
      intro E
      apply SetLike.coe_injective
      change e.symm '' (e '' (E : Set L)) = E
      ext x
      simp
    right_inv := by
      intro E
      apply SetLike.coe_injective
      change e '' (e.symm '' (E : Set L')) = E
      ext x
      simp
  }
  map_rel_iff' := by
    intro E G
    change e '' (E : Set L) ⊆ e '' (G : Set L) ↔ (E : Set L) ⊆ G
    exact Set.image_subset_image_iff e.injective

end ClassFieldTheory

end
