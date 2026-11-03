/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LubinTate/EqualCharacteristic/NormSubgroup/StandardSubgroupNorm.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitsNorm
public import Submissions.gao_general_number_fields_9672.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# LubinTate the explicit norm-subgroup computation: the sharp standard subgroup consists of norms

The higher-unit norm calculation and the uniformizer norm combine to give
the division-level inclusion `(T⁻¹) × U^(n+1) ≤ N(L_n/K)`.
-/

noncomputable section


open scoped LaurentSeries PowerSeries ValuativeRel

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory

open LocalFieldTheory.DiscreteValuationField

variable {K : Type} [Field K]

/-- The canonical field principal-unit subgroup `U^(n+1)` consists of
norms from the standard level. -/
theorem equalCharacteristicLubinTate_fieldPrincipalUnits_le_normSubgroup
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    letI : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    LocalFieldTheory.fieldPrincipalUnits F.residueField⸨X⸩ (n + 1) ≤
      equalCharacteristicLubinTateNormSubgroup F n := by
  let : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  rw [← equalCharacteristicLubinTateHigherUnitSubgroup_map_toLaurentField_eq]
  rintro x ⟨a, ha, rfl⟩
  exact
    equalCharacteristicPowerSeriesUnitToLaurentFieldUnit_mem_normSubgroup_of_mem_higherUnit
      F n a ha

/-- The sharp standard subgroup `(T⁻¹) × U^(n+1)` is contained in the norm
subgroup. -/
theorem
    equalCharacteristicLubinTate_uniformizerPrincipalSubgroup_le_normSubgroup
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    letI : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    LocalFieldTheory.uniformizerPrincipalSubgroup F.residueField⸨X⸩
        ((equalCharacteristicLaurentUniformizerUnit F)⁻¹) 1 (n + 1) ≤
      equalCharacteristicLubinTateNormSubgroup F n := by
  let : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  rw [LocalFieldTheory.uniformizerPrincipalSubgroup]
  apply sup_le
  · simpa using
      equalCharacteristicLubinTate_normalizedUniformizer_zpowers_le_normSubgroup
        F n
  · exact
      equalCharacteristicLubinTate_fieldPrincipalUnits_le_normSubgroup F n

end EqualCharacteristic
end LubinTate

end
