/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/OrdinaryNarrowModuliEqOfNoReal.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.OrdinaryRayClassModulus
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Ordinary and narrow moduli without real places
-/

namespace ClassFieldTheory

universe u

/-- If the base number field has no real places, the ordinary and narrow
class-group moduli coincide. -/
theorem ordinaryRayClassModulus_eq_narrow_of_noReal
    (K : Type u) [Field K] [NumberField K]
    [IsEmpty (RayClassRealPlace K)] :
    ordinaryRayClassModulus K = narrowRayClassModulus K := by
  classical
  have h : (Finset.univ : Finset (RayClassRealPlace K)) = ∅ := by
    ext v
    exact isEmptyElim v
  unfold ordinaryRayClassModulus narrowRayClassModulus
  rw [h]

end ClassFieldTheory
