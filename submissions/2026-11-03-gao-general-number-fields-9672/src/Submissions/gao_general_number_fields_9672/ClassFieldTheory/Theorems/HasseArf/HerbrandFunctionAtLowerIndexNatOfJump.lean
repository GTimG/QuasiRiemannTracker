/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HasseArf/HerbrandFunctionAtLowerIndexNatOfJump.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.HasseArf.HerbrandFunctionAtLowerIndex
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.HasseArf.IsLowerRamificationJump
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.HasseArf
public import Mathlib.NumberTheory.LocalField.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Natural Herbrand values at lower ramification jumps

The finite-sum Herbrand value is nonnegative at every integral lower index.
For a finite Abelian extension of nonarchimedean local fields, Hasse--Arf
therefore makes the value at each lower jump a natural number.
-/

namespace ClassFieldTheory

universe u v

/-- The rational Herbrand value at any integral lower index is nonnegative. -/
private theorem herbrandFunctionAtLowerIndex_nonneg
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (n : ℕ) :
    0 ≤ herbrandFunctionAtLowerIndex K A n := by
  unfold herbrandFunctionAtLowerIndex
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i hi
    exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _

/-- At an integral lower ramification jump of a finite Abelian local
extension, the rational Herbrand value is a natural number. -/
theorem herbrandFunctionAtLowerIndex_eq_nat_of_isLowerRamificationJump
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    {n : ℕ}
    (hn : IsLowerRamificationJump K
      (ValuativeRel.valuation L).valuationSubring n) :
    ∃ m : ℕ,
      herbrandFunctionAtLowerIndex K
        (ValuativeRel.valuation L).valuationSubring n = (m : ℚ) := by
  obtain ⟨z, hz⟩ := ClassFieldTheory.hasseArf K L hn
  have hznonneg : 0 ≤ z := by
    have hnonneg := herbrandFunctionAtLowerIndex_nonneg K
      (ValuativeRel.valuation L).valuationSubring n
    rw [hz] at hnonneg
    exact_mod_cast hnonneg
  refine ⟨z.toNat, ?_⟩
  calc
    herbrandFunctionAtLowerIndex K
        (ValuativeRel.valuation L).valuationSubring n = (z : ℚ) := hz
    _ = ((z.toNat : ℕ) : ℚ) := by
      exact_mod_cast (Int.natCast_toNat_eq_self.mpr hznonneg).symm

end ClassFieldTheory
