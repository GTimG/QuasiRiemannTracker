/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldUniqueUpToEquiv.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldUnique

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Small Hilbert class fields are isomorphic

The intrinsic maximality condition determines a small Hilbert class field up to
an isomorphism over the base.  This asserts existence of an isomorphism, not a
distinguished or unique choice of one.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

/-- Any two small Hilbert class fields are isomorphic over the base field.
The isomorphism itself need not be unique. -/
theorem smallHilbertClassFields_equiv
    (K : Type u) [Field K] [NumberField K]
    (E F : FiniteAbelianExtension K)
    (hE : IsSmallHilbertClassField E)
    (hF : IsSmallHilbertClassField F) :
    Nonempty (E ≃ₐ[K] F) := by
  have hEF : E = F :=
    Subtype.ext (smallHilbertClassFields_eq K E F hE hF)
  cases hEF
  exact ⟨AlgEquiv.refl⟩

end ClassFieldTheory

end
