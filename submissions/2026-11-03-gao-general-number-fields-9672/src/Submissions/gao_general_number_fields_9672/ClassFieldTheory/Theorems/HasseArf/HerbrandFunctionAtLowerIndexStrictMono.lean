/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HasseArf/HerbrandFunctionAtLowerIndexStrictMono.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.HasseArf.HerbrandFunctionAtLowerIndex
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.HasseArf
public import Mathlib.Order.Monotone.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Strict growth of the integral-index Herbrand function

For a finite extension, each lower ramification group is finite and
nonempty. Thus every increment of the rational Herbrand function is
strictly positive. This does not assert integrality of its values.
-/

namespace ClassFieldTheory

universe u v

/-- The rational Herbrand function at nonnegative integral lower indices is
strictly increasing for a finite field extension. -/
theorem herbrandFunctionAtLowerIndex_strictMono
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (A : ValuationSubring L) :
    StrictMono (herbrandFunctionAtLowerIndex K A) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [herbrandFunctionAtLowerIndex_succ]
  have hnum : 0 < (Nat.card (lowerRamificationGroup K A (n + 1)) : ℚ) := by
    exact_mod_cast Nat.card_pos (α := lowerRamificationGroup K A (n + 1))
  have hden : 0 < (Nat.card (lowerRamificationGroup K A 0) : ℚ) := by
    exact_mod_cast Nat.card_pos (α := lowerRamificationGroup K A 0)
  exact lt_add_of_pos_right _ (div_pos hnum hden)

end ClassFieldTheory
