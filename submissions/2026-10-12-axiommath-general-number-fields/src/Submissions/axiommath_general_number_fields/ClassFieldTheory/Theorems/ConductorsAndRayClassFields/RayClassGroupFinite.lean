/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassGroupFinite.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Finiteness of the ideal-theoretic ray class group

The comparison with the idèlic ray class group identifies this group with a
quotient by a finite-index congruence subgroup, so it is finite for every
modulus.
-/

namespace ClassFieldTheory

universe u

/-- Every ray class group of a number field is finite. -/
theorem rayClassGroup_finite
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) :
    Finite (RayClassGroup m) := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  let : Finite (RayClass.RayClassGroup m') := inferInstance
  exact Finite.of_equiv (RayClass.RayClassGroup m')
    (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm.toEquiv

end ClassFieldTheory
