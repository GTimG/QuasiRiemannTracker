/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/HasseArf/IsUpperRamificationJump.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.HasseArf.UpperRamificationGroup

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Upper ramification jumps

The right-limit group is the supremum of upper groups at strictly larger
indices. A jump occurs exactly when that right limit differs from the group
at the index itself.
-/

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The upper ramification group immediately after a real index. -/
def upperRamificationGroupAfter
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) :
    Subgroup (((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K) :=
  ⨆ s : {s : ℝ // t < s}, upperRamificationGroup K L s

/-- A real upper index is a jump when the upper filtration changes
immediately to its right. -/
def IsUpperRamificationJump
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) : Prop :=
  upperRamificationGroup K L t ≠ upperRamificationGroupAfter K L t

end ClassFieldTheory

end
