/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HasseArf/UpperRamificationGroupAntitone.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HasseArf.UpperRamificationGroup
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Theorems.HasseArf.HerbrandFunctionCanonical
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Theorems.HasseArf.HerbrandFunctionInverseHerbrandFunction
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Theorems.HasseArf.RealLowerRamificationGroupCanonical

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-! # Antitonicity of the canonical upper filtration -/

namespace ClassFieldTheory

/-- The public canonical upper ramification filtration decreases with its
real upper index. -/
theorem upperRamificationGroup_antitone
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Antitone (upperRamificationGroup K L) := by
  intro s t hst
  have hpsi : inverseHerbrandFunction K L s ≤ inverseHerbrandFunction K L t := by
    apply (herbrandFunction_canonical_strictMono K L).le_iff_le.mp
    rw [herbrandFunction_inverseHerbrandFunction K L s,
      herbrandFunction_inverseHerbrandFunction K L t]
    exact hst
  exact (realLowerRamificationGroup_canonical_antitone K L) hpsi

end ClassFieldTheory
