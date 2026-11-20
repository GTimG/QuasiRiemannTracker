/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HilbertSymbols/PowerClassInv.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Inversion of power classes

The quotient map to power classes preserves inverses.
-/

namespace ClassFieldTheory

universe u

/-- The class of an inverse is the inverse class. -/
@[simp]
theorem powerClass_inv
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) :
    powerClass K n a⁻¹ = (powerClass K n a)⁻¹ :=
  map_inv (powerClass K n) a

end ClassFieldTheory
