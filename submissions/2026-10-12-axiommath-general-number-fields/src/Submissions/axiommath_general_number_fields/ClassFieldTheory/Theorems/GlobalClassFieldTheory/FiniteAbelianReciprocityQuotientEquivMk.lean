/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/GlobalClassFieldTheory/FiniteAbelianReciprocityQuotientEquivMk.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityQuotientEquiv

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Evaluation of the finite Artin quotient isomorphism

The induced isomorphism maps the class of a ray class to its Artin value.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The quotient isomorphism evaluates to the original Artin map. -/
@[simp]
theorem finiteAbelianReciprocityQuotientEquiv_mk
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L)
    (x : RayClassGroup D.modulus) :
    finiteAbelianReciprocityQuotientEquiv K L D
        (QuotientGroup.mk' D.artin.ker x) = D.artin x := by
  rfl

end ClassFieldTheory

end
