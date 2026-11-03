/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/HilbertSymbols/HilbertPairingNormResidueCriterion.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingSymbol
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HilbertSymbols.IsKummerNorm

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The norm-residue criterion
-/

namespace ClassFieldTheory.HilbertPairing

universe u

/-- The symbol of `a` and `b` is one exactly when `b` is a norm from the
Kummer algebra of `a`. -/
def SatisfiesNormResidueCriterion
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) : Prop :=
  ∀ a b : Kˣ, B.symbol a b = 1 ↔ IsKummerNorm K n a b

end ClassFieldTheory.HilbertPairing
