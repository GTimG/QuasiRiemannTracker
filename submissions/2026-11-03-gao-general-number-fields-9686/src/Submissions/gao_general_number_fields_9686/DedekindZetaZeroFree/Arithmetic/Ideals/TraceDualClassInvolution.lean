/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Ideals/TraceDualClassInvolution.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.Ideals.TraceDualIdeal
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LFunctions.Dedekind.IdealClassConeSeries

@[expose] public section

/-
https://github.com/LeanPool/lean-pool
Revision: 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Source: LeanPool/Odlyzko/CompletedZeta/TraceDualClass.lean.
-/

noncomputable section

open scoped NumberField nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

def principalTraceDualClass (F : Type) [Field F] [NumberField F] : ClassGroup (𝓞 F) :=
  ClassGroup.mk F (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F 1)

theorem mk_traceDualIdealUnit (F : Type) [Field F] [NumberField F]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    ClassGroup.mk F (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F I) =
      principalTraceDualClass F * (ClassGroup.mk F I)⁻¹ := by
  have h : DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F I =
      DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F 1 * I⁻¹ := by
    apply Units.ext
    simpa using
      DedekindZetaZeroFree.AbelianQuotient.Theta.coe_traceDualIdealUnit_eq_dual_one_mul_inv F I
  rw [h, map_mul, map_inv]
  rfl

def principalTraceDualClassEquiv (F : Type) [Field F] [NumberField F] :
    ClassGroup (𝓞 F) ≃ ClassGroup (𝓞 F) where
  toFun C := (principalTraceDualClass F)⁻¹ * C⁻¹
  invFun C := (principalTraceDualClass F)⁻¹ * C⁻¹
  left_inv := by
    intro C
    simp [mul_inv_rev, mul_comm, mul_left_comm]
  right_inv := by
    intro C
    simp [mul_inv_rev, mul_comm, mul_left_comm]

@[simp] theorem principalTraceDualClassEquiv_apply (F : Type) [Field F] [NumberField F]
    (C : ClassGroup (𝓞 F)) :
    principalTraceDualClassEquiv F C = (principalTraceDualClass F)⁻¹ * C⁻¹ := rfl

@[simp] theorem principalTraceDualClassEquiv_symm_apply (F : Type)
    [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) :
    (principalTraceDualClassEquiv F).symm C = (principalTraceDualClass F)⁻¹ * C⁻¹ := rfl

theorem mk_traceDual_inverseClassIdealRepresentative (F : Type) [Field F] [NumberField F]
    (C : ClassGroup (𝓞 F)) :
    ClassGroup.mk F
      (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F
        (FractionalIdeal.mk0 F
          (DedekindZetaZeroFree.AbelianQuotient.Theta.inverseClassIdealRepresentative F C))) =
    ClassGroup.mk F
      (FractionalIdeal.mk0 F
        (DedekindZetaZeroFree.AbelianQuotient.Theta.inverseClassIdealRepresentative F
          (principalTraceDualClassEquiv F C))) := by
  rw [mk_traceDualIdealUnit, ClassGroup.mk_mk0, ClassGroup.mk_mk0]
  simp [DedekindZetaZeroFree.AbelianQuotient.Theta.mk0_inverseClassIdealRepresentative,
    mul_inv_rev, mul_comm]

end DedekindZetaZeroFree.Hecke

end
