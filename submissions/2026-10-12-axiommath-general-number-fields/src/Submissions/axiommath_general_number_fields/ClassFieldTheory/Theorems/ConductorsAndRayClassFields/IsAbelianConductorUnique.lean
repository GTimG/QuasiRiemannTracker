/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/IsAbelianConductorUnique.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Uniqueness of the conductor

A finite abelian extension has at most one modulus that characterizes exactly
the ray class fields containing it.
-/

namespace ClassFieldTheory

universe u v

/-- The least modulus characterized by ray-class-field containment is unique. -/
theorem IsAbelianConductor.unique
    {K : Type u} [Field K] [NumberField K]
    {L : Type v} [Field L] [NumberField L] [Algebra K L]
    {c d : RayClassModulus K}
    (hc : IsAbelianConductor K L c)
    (hd : IsAbelianConductor K L d) : c = d := by
  apply le_antisymm
  · exact (hc d).mp ((hd d).mpr le_rfl)
  · exact (hd c).mp ((hc c).mpr le_rfl)

end ClassFieldTheory
