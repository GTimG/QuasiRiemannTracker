/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/HilbertSymbols/HilbertPairingSymbol.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairing
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Evaluation of a Hilbert pairing on representatives
-/

namespace ClassFieldTheory.HilbertPairing

universe u

/-- Evaluate a power-class pairing on representatives in `Kˣ`. -/
def symbol
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) (a b : Kˣ) :
    rootsOfUnity (n : ℕ) K :=
  B (powerClass K n a) (powerClass K n b)

end ClassFieldTheory.HilbertPairing
