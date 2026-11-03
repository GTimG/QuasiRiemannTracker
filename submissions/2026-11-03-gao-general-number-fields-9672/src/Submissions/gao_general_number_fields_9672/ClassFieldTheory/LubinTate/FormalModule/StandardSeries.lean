/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LubinTate/FormalModule/StandardSeries.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# The standard Lubin--Tate series

For a uniformizer `π`, the polynomial power series

`π X + X ^ q`,

where `q` is the cardinality of the residue field, is a Lubin--Tate
series.  This gives the general formal-module construction a canonical
polynomial input without making an equal-characteristic assumption.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- The polynomial power series `π X + X ^ q`, where `q` is the residue
field cardinality. -/
noncomputable def standardLubinTatePowerSeries
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    PowerSeries F.valuationSubring :=
  PowerSeries.C π * PowerSeries.X +
    PowerSeries.X ^ Nat.card F.residueField

/-- A uniformizer makes `π X + X ^ q` into a Lubin--Tate series. -/
noncomputable def standardLubinTateSeries
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    LubinTateSeries F π where
  toPowerSeries := standardLubinTatePowerSeries F π
  constantCoeff_eq_zero := by
    have hq0 : Nat.card F.residueField ≠ 0 :=
      Nat.ne_of_gt (lt_trans Nat.zero_lt_one
        (Finite.one_lt_card (α := F.residueField)))
    simp [standardLubinTatePowerSeries, hq0]
  coeff_one_eq_uniformizer := by
    have hq : 1 ≠ Nat.card F.residueField :=
      (Finite.one_lt_card (α := F.residueField)).ne
    simp [standardLubinTatePowerSeries, PowerSeries.coeff_X_pow, hq]
  map_residue_eq_frobenius := by
    simp [standardLubinTatePowerSeries,
      SameUniformizer.residueMap_uniformizer_eq_zero hπ]

namespace LubinTateSeries

/-- The underlying series of the standard Lubin--Tate input is literally
`π X + X ^ q`. -/
@[simp]
theorem standardLubinTateSeries_toPowerSeries
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    (standardLubinTateSeries hπ).toPowerSeries =
      standardLubinTatePowerSeries F π :=
  rfl

end LubinTateSeries
end LubinTate

end
