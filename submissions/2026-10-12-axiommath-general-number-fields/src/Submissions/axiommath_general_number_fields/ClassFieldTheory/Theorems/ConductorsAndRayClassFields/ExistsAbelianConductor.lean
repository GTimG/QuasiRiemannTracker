/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/ExistsAbelianConductor.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.EmbedsInRayClassFieldIffConductorLe
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Existence of the abelian conductor

The conductor of a finite abelian extension is the least modulus whose ray
class field contains that extension. The older theorem name
`embedsInRayClassField_iff_conductor_le` remains available for compatibility;
its conclusion is an existence statement, so this name reflects its type.
-/

namespace ClassFieldTheory

/-- A finite abelian extension of number fields has a conductor. -/
theorem exists_abelianConductor
    (K : Type) [Field K] [NumberField K]
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] :
    ∃ c : RayClassModulus K, IsAbelianConductor K L c :=
  embedsInRayClassField_iff_conductor_le K L

end ClassFieldTheory
