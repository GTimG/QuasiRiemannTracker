/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HasseArf/HerbrandFunctionAtLowerIndexDifference.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HasseArf.HerbrandFunctionAtLowerIndex
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.HasseArf

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Herbrand-function increment at integral lower indices

The sum starts at index one: the increment from `n` to `n + 1` is the
cardinality of the next lower group divided by that of the zeroth group.
-/

namespace ClassFieldTheory

universe u v

/-- The difference of successive rational Herbrand values is the
normalized size of the next lower ramification group. -/
theorem herbrandFunctionAtLowerIndex_difference
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (n : ℕ) :
    herbrandFunctionAtLowerIndex K A (n + 1) -
        herbrandFunctionAtLowerIndex K A n =
      (Nat.card (lowerRamificationGroup K A (n + 1)) : ℚ) /
        Nat.card (lowerRamificationGroup K A 0) := by
  rw [herbrandFunctionAtLowerIndex_succ]
  ring

end ClassFieldTheory
