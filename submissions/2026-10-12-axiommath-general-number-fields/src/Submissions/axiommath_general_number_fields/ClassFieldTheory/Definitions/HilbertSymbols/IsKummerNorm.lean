/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/HilbertSymbols/IsKummerNorm.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
public import Mathlib.RingTheory.Norm.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Norms from Kummer algebras
-/

namespace ClassFieldTheory

universe u

/-- A nonzero element `b` is a norm from the Kummer algebra
`K[X] / (X^n - a)`. -/
def IsKummerNorm
    (K : Type u) [Field K] (n : ℕ+) (a b : Kˣ) : Prop :=
  ∃ y : (KummerAlgebra K n a)ˣ,
    Algebra.norm K (y : KummerAlgebra K n a) = (b : K)

end ClassFieldTheory
