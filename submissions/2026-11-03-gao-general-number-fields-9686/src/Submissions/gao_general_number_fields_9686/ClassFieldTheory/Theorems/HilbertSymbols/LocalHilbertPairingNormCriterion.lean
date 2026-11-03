/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HilbertSymbols/LocalHilbertPairingNormCriterion.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairing
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingSymbol
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HilbertSymbols.IsKummerNorm
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Norm-residue criterion for a local Hilbert pairing

The vanishing of a local Hilbert symbol is equivalent to a concrete Kummer
norm condition.  The Kummer algebra is the canonical Mathlib quotient
`K[X] / (X^n - a)`, so the statement does not choose a root in an algebraic
closure.
-/

namespace ClassFieldTheory

universe u

/-- A local Hilbert pairing evaluates to one exactly on Kummer norms. -/
theorem localHilbertPairing_eq_one_iff_isKummerNorm
    (K : Type u) [Field K] (n : ℕ+)
    (B : HilbertPairing K n)
    (hB : HilbertPairing.IsLocalHilbertPairing B)
    (a b : Kˣ) :
    B.symbol a b = 1 ↔ IsKummerNorm K n a b := by
  exact hB.2.2.2 a b

end ClassFieldTheory
