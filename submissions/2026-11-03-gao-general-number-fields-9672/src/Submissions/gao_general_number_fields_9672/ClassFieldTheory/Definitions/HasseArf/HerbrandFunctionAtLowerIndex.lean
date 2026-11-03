/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/HasseArf/HerbrandFunctionAtLowerIndex.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.HasseArf.LowerRamificationGroup
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Finset.Interval
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# The Herbrand function at integral lower indices
-/

open scoped BigOperators

noncomputable section

namespace ClassFieldTheory

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

/-- The Herbrand value at a nonnegative integral lower index:
`φ(n) = (1 / |G₀|) · ∑_{i=1}^{n} |Gᵢ|`.

Its ramification-theoretic interpretation requires the lower groups to be
finite.  The definition alone does not impose that hypothesis. -/
def herbrandFunctionAtLowerIndex (A : ValuationSubring L) (n : ℕ) : ℚ :=
  (∑ i ∈ Finset.Icc 1 n,
      (Nat.card (lowerRamificationGroup K A i) : ℚ)) /
    (Nat.card (lowerRamificationGroup K A 0) : ℚ)

end ClassFieldTheory

end
