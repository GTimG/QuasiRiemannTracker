/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HasseArf/HerbrandFunctionNat.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.HasseArf.HerbrandFunction

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-! # Herbrand values at natural lower indices -/

noncomputable section

namespace ClassFieldTheory

universe u v

/-- At a natural lower index, the real piecewise Herbrand function equals
the rational finite-sum value after casting to reals. -/
theorem herbrandFunction_nat
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (n : ℕ) :
    ClassFieldTheory.herbrandFunction K A (n : ℝ) =
      (herbrandFunctionAtLowerIndex K A n : ℝ) := by
  unfold ClassFieldTheory.herbrandFunction
  rw [ite_eq_left (Nat.cast_nonneg n)]
  dsimp only
  rw [Nat.floor_natCast, sub_self, zero_mul, add_zero]

end ClassFieldTheory

end
