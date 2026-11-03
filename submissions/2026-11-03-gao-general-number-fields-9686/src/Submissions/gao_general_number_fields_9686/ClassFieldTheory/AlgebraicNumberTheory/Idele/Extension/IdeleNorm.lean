/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/IdeleNorm.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The norm on ordinary ideles

The relative idele group carries the determinant norm.  The
scalar-extension equivalence with the ordinary ideles of the extension
field transports that existing norm to the usual map
`N_{L/K} : I_L → I_K`.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The ordinary idele norm `N_{L/K} : I_L → I_K`, transported from
the determinant norm on the relative idele group. -/
noncomputable def norm :
    IdeleGroup L →* IdeleGroup K :=
  (RelativeIdeleGroup.norm K L).comp
    (relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)).symm.toMonoidHom

@[simp]
theorem norm_relativeIdeleBaseChangeMulEquiv
    (z : RelativeIdeleGroup K L) :
    norm K L
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z) =
      RelativeIdeleGroup.norm K L z := by
  simp [norm]

/-- On principal ideles, the ordinary idele norm is induced by the
field norm. -/
@[simp]
theorem norm_principalIdele
    (x : Lˣ) :
    norm K L (principalIdele L x) =
      principalIdele K (Units.map (Algebra.norm K) x) := by
  rw [← relativeIdeleBaseChangeMulEquiv_principalIdele
    (K := K) (L := L) x]
  rw [norm_relativeIdeleBaseChangeMulEquiv,
    RelativeIdeleGroup.norm_principalIdele]

end IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The ordinary idele-class norm `N_{L/K} : C_L → C_K`. -/
noncomputable def ideleClassNorm :
    IdeleClassGroup L →* IdeleClassGroup K :=
  QuotientGroup.map
    (IdeleGroup.principalSubgroup L)
    (IdeleGroup.principalSubgroup K)
    (IdeleGroup.norm K L)
    (by
      rintro _ ⟨x, rfl⟩
      exact
        ⟨Units.map (Algebra.norm K) x,
          (IdeleGroup.norm_principalIdele K L x).symm⟩)

@[simp]
theorem ideleClassNorm_mk
    (a : IdeleGroup L) :
    ideleClassNorm K L
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup L) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.norm K L a) :=
  rfl

end
