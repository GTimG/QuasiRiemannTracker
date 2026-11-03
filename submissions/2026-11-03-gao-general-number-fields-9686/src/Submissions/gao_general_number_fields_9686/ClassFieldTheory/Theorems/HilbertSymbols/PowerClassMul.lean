/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HilbertSymbols/PowerClassMul.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Multiplication of power classes

The quotient map to power classes preserves multiplication.
-/

namespace ClassFieldTheory

universe u

/-- The class of a product is the product of the classes. -/
@[simp]
theorem powerClass_mul
    (K : Type u) [Field K] (n : ℕ+) (a b : Kˣ) :
    powerClass K n (a * b) = powerClass K n a * powerClass K n b :=
  map_mul (powerClass K n) a b

end ClassFieldTheory
