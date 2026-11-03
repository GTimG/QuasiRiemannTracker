/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/GlobalClassFieldTheory/FiniteAbelianReciprocityQuotientEquiv.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The quotient induced by a finite Artin map

This is the specific isomorphism induced by the Artin map in
`FiniteAbelianReciprocityData`, not an arbitrarily chosen isomorphism.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The first-isomorphism-theorem map induced by a finite Artin map. -/
def finiteAbelianReciprocityQuotientEquiv
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    (RayClassGroup D.modulus ⧸ D.artin.ker) ≃* (L ≃ₐ[K] L) :=
  QuotientGroup.quotientKerEquivOfSurjective D.artin D.artin_surjective

end ClassFieldTheory

end
