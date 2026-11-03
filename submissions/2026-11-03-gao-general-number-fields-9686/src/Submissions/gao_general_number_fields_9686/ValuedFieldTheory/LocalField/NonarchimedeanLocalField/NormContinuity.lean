/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormContinuity.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ValuedFieldTheory.LocalField.NormUnits
public import Submissions.gao_general_number_fields_9686.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Continuity of finite field norms

This module records the analytic input used by the topological finite local
reciprocity law: on a finite-dimensional normed algebra, the field norm is a
determinant and is therefore continuous.  It also bundles the corresponding
statements for field units and valuation-ring units.
-/

noncomputable section

universe u v

namespace LocalFieldTheory

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The field norm of a finite-dimensional normed algebra over a complete
nontrivially normed field is continuous. -/
theorem algebraNorm_continuous_of_finiteDimensional
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NormedField L]
    [Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ContinuousSMul K L] :
    Continuous (Algebra.norm K : L → K) := by
  classical
  let b := Module.Free.chooseBasis K L
  rw [show (Algebra.norm K : L → K) =
      fun x => (Algebra.leftMulMatrix b x).det by
    funext x
    exact Algebra.norm_eq_matrix_det b x]
  apply Continuous.matrix_det
  exact (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional

/-- The field norm induced on unit groups is continuous. -/
theorem normUnits_continuous_of_finiteDimensional
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NormedField L]
    [Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ContinuousSMul K L] :
    Continuous (normUnits K L) := by
  unfold normUnits
  exact Continuous.units_map (Algebra.norm K : L →* K)
    (algebraNorm_continuous_of_finiteDimensional K L)

/-- The canonical inclusion from valuation-ring units to field units is
continuous for the subtype topologies. -/
theorem integerUnitsToFieldUnits_continuous
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] :
    Continuous (integerUnitsToFieldUnits K) := by
  unfold IsNonarchimedeanLocalField.integerUnitsToFieldUnits
  exact Continuous.units_map
    ((algebraMap 𝒪[K] K).toMonoidHom) continuous_subtype_val

end LocalFieldTheory

end
