/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LubinTate/EqualCharacteristic/NormSubgroup/HigherUnitFixedFieldEquiv.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# LubinTate the explicit norm-subgroup computation: the standard level is the higher-unit fixed field

The standard-level embedding is an equivalence because its source and target
have the same degree `(q - 1) q^n`.
-/

noncomputable section


open scoped LaurentSeries PowerSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type} [Field K]

attribute [local instance]
  equalCharacteristicCompletedFrobeniusFixedBaseAlgebra
  equalCharacteristicLubinTateLevelFieldAlgebra
  equalCharacteristicLubinTateLevelFieldSMul
  equalCharacteristicLubinTateLevelFieldModule
  equalCharacteristicCompletedFrobeniusFixedFieldAlgebra
  equalCharacteristicCompletedFrobeniusFixedFieldSMul
  equalCharacteristicCompletedFrobeniusFixedFieldModule

/-- Defines `equalCharacteristicLubinTateLevelFieldEquivFixedFieldOfHigherUnit`. -/
noncomputable def
    equalCharacteristicLubinTateLevelFieldEquivFixedFieldOfHigherUnit
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n) :
    @AlgEquiv
      F.residueField⸨X⸩
      ↥(equalCharacteristicLubinTateLevelField F n)
      ↥(equalCharacteristicCompletedFrobeniusFixedField F a n)
      inferInstance
      inferInstance
      inferInstance
      (equalCharacteristicLubinTateLevelFieldAlgebra F n)
      (equalCharacteristicCompletedFrobeniusFixedFieldAlgebra F a n) :=
  AlgEquiv.ofBijective
    (equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnit F a n ha)
    ⟨fun _ _ h =>
      (equalCharacteristicLubinTateLevelFieldToCompletedRingHom F n).injective
        (congrArg Subtype.val h),
      equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnit_surjective
        F a n ha⟩

end EqualCharacteristic
end LubinTate

end
