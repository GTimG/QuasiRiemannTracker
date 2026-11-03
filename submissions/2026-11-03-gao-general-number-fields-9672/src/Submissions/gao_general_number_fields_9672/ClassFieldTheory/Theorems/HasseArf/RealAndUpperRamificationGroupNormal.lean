/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HasseArf/RealAndUpperRamificationGroupNormal.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.HasseArf.UpperRamificationGroup
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.RealLowerRamificationGroupNormal

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Normality of real lower and upper ramification groups

Upper groups are real lower groups evaluated at inverse Herbrand indices,
so their normality follows from normality of the real lower groups.
-/

namespace ClassFieldTheory

universe u v

/-- Each canonical real upper ramification group is normal in its
decomposition group. -/
theorem upperRamificationGroup_normal
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) :
    (upperRamificationGroup K L t).Normal :=
  realLowerRamificationGroup_normal K
    (ValuativeRel.valuation L).valuationSubring
    (inverseHerbrandFunction K L t)

end ClassFieldTheory
