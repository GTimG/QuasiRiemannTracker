/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/FullConductorRayClassField.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorInfinitePart
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Full conductors and ray class field containment

This module identifies the full conductor of a finite abelian extension
as the least modulus of a selected ray class field into which the extension
embeds.  The proof combines the ray-field embedding criterion with the
minimality theorem for the full conductor.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable {K : Type} [Field K] [NumberField K]

/-- A finite abelian extension embeds in the selected ray class field
exactly when the modulus is at least its full conductor. -/
theorem nonempty_algHom_to_rayClassField_iff_fullConductor_le
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]
    (m : RayClass.Modulus K) :
    Nonempty (L →ₐ[K] rayClassField K m) ↔
      (ideleClassNormConductorialSubgroup
        (K := K) (L := L)).fullConductor ≤ m := by
  rw [nonempty_algHom_to_rayClassField_iff_isDefiningModulus]
  exact
    (ideleClassNormConductorialSubgroup
      (K := K) (L := L)).isDefiningModulus_iff_fullConductor_le m

end GlobalClassFields
end GlobalClassFieldTheory

end
