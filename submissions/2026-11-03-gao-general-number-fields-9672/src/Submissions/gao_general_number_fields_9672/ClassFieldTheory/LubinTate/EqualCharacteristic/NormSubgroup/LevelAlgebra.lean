/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LubinTate/EqualCharacteristic/NormSubgroup/LevelAlgebra.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
public import Submissions.gao_general_number_fields_9672.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# LubinTate the explicit norm-subgroup computation: canonical algebra and norm subgroup at a finite level

This light leaf names the canonical base algebra and its norm subgroup once,
so the later inclusion and index arguments do not repeat expensive fallback
typeclass searches.
-/

noncomputable section


open scoped LaurentSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type} [Field K]

noncomputable local instance equalCharacteristicLaurentSeriesField
    (F : LocalField K) : Field F.residueField⸨X⸩ :=
  @HahnSeries.instField ℤ F.residueField Int.instAddCommGroup
    Int.instLinearOrder Int.instIsOrderedAddMonoid inferInstance

noncomputable local instance equalCharacteristicLaurentSeriesMonoid
    (F : LocalField K) : Monoid F.residueField⸨X⸩ :=
  @CommMonoid.toMonoid F.residueField⸨X⸩
    (@CommRing.toCommMonoid F.residueField⸨X⸩
      (@Field.toCommRing F.residueField⸨X⸩
        (equalCharacteristicLaurentSeriesField F)))

attribute [local instance]
  equalCharacteristicLubinTateLevelFieldAlgebra
  equalCharacteristicLubinTateLevelFieldSMul
  equalCharacteristicLubinTateLevelFieldModule

/-- The canonical base algebra on the explicit Lubin--Tate level field. -/
@[reducible] noncomputable def equalCharacteristicLubinTateLevelAlgebra
    (F : LocalField K) [CharP K F.residueCharacteristic] (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelFieldAlgebra F n

/-- The norm subgroup of the explicit Lubin--Tate level, with the canonical
base algebra fixed once for downstream statements. -/
noncomputable def equalCharacteristicLubinTateNormSubgroup
    (F : LocalField K) [CharP K F.residueCharacteristic] (n : ℕ) :
    Subgroup F.residueField⸨X⸩ˣ := by
  letI : Algebra F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelAlgebra F n
  exact LocalFieldTheory.localNormSubgroup F.residueField⸨X⸩
    (equalCharacteristicLubinTateLevelField F n)

end EqualCharacteristic
end LubinTate

end
