/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/AbelianConductorRayClassFieldLe.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The conductor of a ray class field

The conductor of the ray class field for a modulus `m` is bounded above by
`m`. Equality need not hold: a modulus may contain redundant conditions.
-/

namespace ClassFieldTheory

universe u

/-- A ray class field's conductor is at most its defining modulus. -/
theorem IsAbelianConductor.le_rayClassFieldModulus
    {K : Type u} [Field K] [NumberField K]
    {m c : RayClassModulus K}
    (R : RayClassFieldRealization K m)
    (hc : IsAbelianConductor K R.extension c) :
    c ≤ m := by
  apply (hc m).mp
  exact ⟨R, ⟨AlgHom.id K R.extension⟩⟩

end ClassFieldTheory
