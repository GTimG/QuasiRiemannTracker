/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HasseArf/UpperRamificationGroupCanonical.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HasseArf.UpperRamificationGroup
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Theorems.HasseArf.InverseHerbrandFunctionHerbrandFunction

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Upper groups at Herbrand indices

The public inverse Herbrand identity identifies the upper group at `φ(s)`
with the public real lower group at `s`.
-/

namespace ClassFieldTheory

/-- The upper group at the Herbrand image of a real lower index is exactly
the corresponding real lower group of the canonical valuation ring. -/
theorem upperRamificationGroup_herbrandFunction
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (s : ℝ) :
    upperRamificationGroup K L
      (herbrandFunction K (ValuativeRel.valuation L).valuationSubring s) =
    realLowerRamificationGroup K
      (ValuativeRel.valuation L).valuationSubring s := by
  unfold upperRamificationGroup
  rw [inverseHerbrandFunction_herbrandFunction K L s]

end ClassFieldTheory
