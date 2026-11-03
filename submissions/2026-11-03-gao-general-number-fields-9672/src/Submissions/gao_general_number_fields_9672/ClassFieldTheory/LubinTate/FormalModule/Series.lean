/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LubinTate/FormalModule/Series.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import Submissions.gao_general_number_fields_9672.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Lubin--Tate power series

A Lubin--Tate power series over a chosen valuation ring has zero constant
coefficient, prescribed linear coefficient, and reduces to the residue-field
Frobenius power series. The chosen element is not required to be a uniformizer
in the structure itself, so the coefficient package can be reused independently.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- A Lubin--Tate series with prescribed linear coefficient π.

The first two fields specify the constant and linear terms. The final field
specifies coefficientwise reduction to the residue-field Frobenius series. -/
structure LubinTateSeries
    (F : LocalField.{u, v} K) (π : F.valuationSubring) where
  /-- The underlying one-variable formal power series over `O_K`. -/
  toPowerSeries : PowerSeries F.valuationSubring
  /-- The constant coefficient of a Lubin--Tate series vanishes. -/
  constantCoeff_eq_zero :
    PowerSeries.constantCoeff toPowerSeries = 0
  /-- The linear coefficient is the chosen element `π`. -/
  coeff_one_eq_uniformizer :
    PowerSeries.coeff 1 toPowerSeries = π
  /-- Reduction to the residue field is the `q`-power Frobenius series. -/
  map_residue_eq_frobenius :
    PowerSeries.map F.residueMap toPowerSeries =
      (PowerSeries.X : PowerSeries F.residueField) ^
        Nat.card F.residueField

attribute [simp] LubinTateSeries.constantCoeff_eq_zero
  LubinTateSeries.coeff_one_eq_uniformizer
  LubinTateSeries.map_residue_eq_frobenius

namespace LubinTateSeries

variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- Two Lubin--Tate series are equal when their underlying power series
are equal. -/
@[ext]
theorem ext {e e' : LubinTateSeries F π}
    (h : e.toPowerSeries = e'.toPowerSeries) : e = e' := by
  cases e
  cases e'
  cases h
  rfl

end LubinTateSeries

end LubinTate

end
