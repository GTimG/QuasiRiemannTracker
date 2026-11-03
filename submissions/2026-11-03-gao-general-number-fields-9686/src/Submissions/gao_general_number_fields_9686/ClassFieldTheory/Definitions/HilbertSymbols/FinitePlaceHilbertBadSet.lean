/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/HilbertSymbols/FinitePlaceHilbertBadSet.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Possible nontrivial finite-place Hilbert factors

This set depends on the two nonzero global arguments and the exponent.  A
finite place is excluded exactly when all three have valuation one there.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u

/-- The places where `a`, `b`, or the exponent is not a valuation-ring unit.
This is the precise finite-place bound for global Hilbert factors. -/
def finitePlaceHilbertBadSet
    (F : Type u) [Field F] [NumberField F]
    (n : ℕ+) (a b : Fˣ) : Set (HeightOneSpectrum (𝓞 F)) :=
  {v | v.valuation F (a : F) ≠ 1 ∨
    v.valuation F (b : F) ≠ 1 ∨
    v.valuation F ((n : ℕ) : F) ≠ 1}

end ClassFieldTheory
