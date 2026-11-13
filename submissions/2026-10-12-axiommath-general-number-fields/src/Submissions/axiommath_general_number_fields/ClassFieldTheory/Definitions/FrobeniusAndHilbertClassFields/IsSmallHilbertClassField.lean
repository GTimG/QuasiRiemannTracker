/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/IsSmallHilbertClassField.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsEverywhereUnramified
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Small Hilbert class fields
-/

namespace ClassFieldTheory

universe u

/-- A small Hilbert class field is an everywhere-unramified finite abelian
extension containing every other such extension. -/
def IsSmallHilbertClassField
    {K : Type u} [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) : Prop :=
  IsEverywhereUnramified K E ∧
    ∀ F : FiniteAbelianExtension K,
      IsEverywhereUnramified K F → Nonempty (F →ₐ[K] E)

end ClassFieldTheory
