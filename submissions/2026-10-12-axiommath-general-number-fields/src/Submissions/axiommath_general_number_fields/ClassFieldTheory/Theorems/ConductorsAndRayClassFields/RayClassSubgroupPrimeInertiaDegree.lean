/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassSubgroupPrimeInertiaDegree.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupQuotientEquiv
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassSubgroupQuotientEquivMk
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusOrder

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Residue degrees in a ray-class subgroup class field

Away from the modulus, the residue degree is the order of the prime ray
class modulo the subgroup defining the extension.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

universe u

/-- The residue degree above a prime away from the modulus is the order of
its ray class in the quotient by the defining subgroup. -/
theorem finitePrime_inertiaDegreeInRayClassSubgroupField_eq_orderOf
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m))
    (R : RayClassSubgroupRealization K m H)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support)
    (w : HeightOneSpectrum (𝓞 R.extension))
    (hw : w.asIdeal.LiesOver v.asIdeal) :
    w.asIdeal.inertiaDeg (𝓞 K) =
      orderOf (QuotientGroup.mk' H (rayClassOfFinitePrime m v hv)) := by
  have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    (R.unramifiedOutsideModulus.1 v hv) w.asIdeal inferInstance hw
  have horder :=
    orderOf_arithmeticFrobeniusAt_eq_inertiaDegree v w hw hunram
  calc
    w.asIdeal.inertiaDeg (𝓞 K) =
        orderOf (arithmeticFrobeniusAt (K := K) w) := horder.symm
    _ = orderOf (R.artin (rayClassOfFinitePrime m v hv)) := by
      rw [R.artin_frobenius v hv w hw]
    _ = orderOf
          (rayClassSubgroupQuotientEquiv K m H R
            (QuotientGroup.mk' H (rayClassOfFinitePrime m v hv))) := by
      rw [rayClassSubgroupQuotientEquiv_mk]
    _ = orderOf (QuotientGroup.mk' H (rayClassOfFinitePrime m v hv)) :=
      (rayClassSubgroupQuotientEquiv K m H R).orderOf_eq _

end ClassFieldTheory

end
