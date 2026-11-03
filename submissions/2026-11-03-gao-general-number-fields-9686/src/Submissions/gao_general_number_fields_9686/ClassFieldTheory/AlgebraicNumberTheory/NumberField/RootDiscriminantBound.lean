/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/NumberField/RootDiscriminantBound.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# From an integral discriminant bound to a root discriminant bound
-/

namespace AlgebraicNumberTheory.DiscriminantBounds

/-- A degree-power bound on the absolute discriminant gives a uniform
bound on the usual real root discriminant. -/
theorem rootDiscr_le_of_natAbs_discr_le_pow
    (F : Type*) [Field F] [NumberField F] (C : ℕ)
    (h : (NumberField.discr F).natAbs ≤ C ^ Module.finrank ℚ F) :
    NumberField.rootDiscr F ≤ (C : ℝ) := by
  have hn : Module.finrank ℚ F ≠ 0 := ne_of_gt Module.finrank_pos
  have hc : ((NumberField.discr F).natAbs : ℝ) ≤
      (C : ℝ) ^ Module.finrank ℚ F := by exact_mod_cast h
  have hd : |(NumberField.discr F : ℝ)| ≤
      (C : ℝ) ^ Module.finrank ℚ F := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hc
  rw [NumberField.rootDiscr_def, Int.cast_abs]
  calc
    |(NumberField.discr F : ℝ)| ^ (Module.finrank ℚ F : ℝ)⁻¹ ≤
        ((C : ℝ) ^ Module.finrank ℚ F) ^ (Module.finrank ℚ F : ℝ)⁻¹ :=
      Real.rpow_le_rpow (abs_nonneg _) hd (by positivity)
    _ = (C : ℝ) := Real.pow_rpow_inv_natCast (by positivity) hn

end AlgebraicNumberTheory.DiscriminantBounds
