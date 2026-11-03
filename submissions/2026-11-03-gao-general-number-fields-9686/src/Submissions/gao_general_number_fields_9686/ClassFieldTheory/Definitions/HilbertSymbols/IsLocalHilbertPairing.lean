/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/HilbertSymbols/IsLocalHilbertPairing.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingLaws
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingNormResidueCriterion

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Local Hilbert pairings
-/

namespace ClassFieldTheory.HilbertPairing

universe u

/-- The algebraic laws and Kummer norm-residue criterion required of a local
Hilbert pairing.  These properties do not fix the value normalization of the
symbol; that requires a comparison with a normalized Artin map. -/
def IsLocalHilbertPairing
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) : Prop :=
  B.IsSteinberg ∧ B.IsSkewSymmetric ∧ B.IsNondegenerate ∧
    B.SatisfiesNormResidueCriterion

end ClassFieldTheory.HilbertPairing
