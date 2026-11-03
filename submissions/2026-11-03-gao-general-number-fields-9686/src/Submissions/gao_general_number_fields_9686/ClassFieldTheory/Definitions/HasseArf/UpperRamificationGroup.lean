/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/HasseArf/UpperRamificationGroup.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HasseArf.InverseHerbrandFunction
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HasseArf.RealLowerRamificationGroup

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Real-index upper ramification groups

The upper group at `t` is the public real lower group at the inverse
Herbrand index `ψ(t)`.
-/

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The upper ramification group of the canonical valuation ring of a
finite Abelian local extension, using the inverse public Herbrand function. -/
def upperRamificationGroup
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) :
    Subgroup (((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K) :=
  realLowerRamificationGroup K
    (ValuativeRel.valuation L).valuationSubring
    (inverseHerbrandFunction K L t)

end ClassFieldTheory

end
