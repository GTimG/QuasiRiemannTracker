/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Idele/NormTopology/IdeleClassNorm.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.ArchimedeanNorm
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdealClass

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# The ordinary norm on idele classes

The ordinary idele-class norm preserves the absolute norm and restricts to
the norm-one idele-class subgroups.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace IdeleClassGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- The ordinary idèle-class norm preserves the absolute idèle norm. -/
theorem absoluteNorm_ideleClassNorm
    (c : IdeleClassGroup L) :
    absoluteNorm (_root_.ideleClassNorm K L c) =
      absoluteNorm c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    absoluteNorm
        (_root_.ideleClassNorm K L
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup L) a)) =
      absoluteNorm
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup L) a)
  rw [_root_.ideleClassNorm_mk,
    absoluteNorm_mk, absoluteNorm_mk,
    IdeleGroup.absoluteNorm_norm]

/-- The ordinary idele-class norm carries norm-one idele classes to
norm-one idele classes. -/
theorem ideleClassNorm_mem_normOneSubgroup
    (c : IdeleClassGroup L)
    (hc : c ∈ normOneSubgroup (K := L)) :
    _root_.ideleClassNorm K L c ∈
      normOneSubgroup (K := K) := by
  change
    absoluteNorm (_root_.ideleClassNorm K L c) = 1
  change absoluteNorm c = 1 at hc
  rw [absoluteNorm_ideleClassNorm]
  exact hc

/-- The ordinary idele-class norm restricted to the norm-one idele-class
groups. -/
noncomputable def normOneNorm :
    normOneSubgroup (K := L) →*
      normOneSubgroup (K := K) :=
  ((_root_.ideleClassNorm K L).comp
      (normOneSubgroup (K := L)).subtype).codRestrict
    (normOneSubgroup (K := K))
    (fun c =>
      ideleClassNorm_mem_normOneSubgroup
        K L c.1 c.2)

/-- Coercing the restricted norm-one map recovers the ordinary idèle-class norm. -/
@[simp]
theorem normOneNorm_apply
    (c : normOneSubgroup (K := L)) :
    (normOneNorm K L c : IdeleClassGroup K) =
      _root_.ideleClassNorm K L c.1 :=
  rfl


end IdeleClassGroup

end
