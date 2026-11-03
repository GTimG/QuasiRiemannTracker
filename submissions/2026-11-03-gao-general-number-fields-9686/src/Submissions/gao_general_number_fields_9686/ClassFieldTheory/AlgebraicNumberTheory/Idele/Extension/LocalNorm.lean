/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/LocalNorm.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import Submissions.gao_general_number_fields_9686.ValuedFieldTheory.Valuation.Completion.DegreeNormTrace
public import Submissions.gao_general_number_fields_9686.ValuedFieldTheory.Valuation.Completion.FiniteProductNormTrace

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Local components of the idele norm

The local algebra at a place of the base field is a finite product of the
completions above it. This file proves that the determinant norm on a finite
product is the product of the norms of its factors. The last theorem applies
this calculation to the canonical completion decomposition.
-/

open scoped BigOperators TensorProduct

noncomputable section


namespace RelativeIdeleGroup

open AlgebraicNumberTheory.Valuations
open ValuationTheory.Completion

universe u v

/-- At one place of the base field, under the
canonical isomorphism

`K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w`,

the determinant norm of an arbitrary local component is the product of
the field norms of its components above `v`. -/
theorem localNorm_eq_prod
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (z : vK.Completion ⊗[K] L) :
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w ↦ completionModuleFinite vK hvK w
    _root_.Algebra.norm vK.Completion z =
      ∏ w : AbsoluteValueExtension vK L,
        _root_.Algebra.norm vK.Completion
          (completionTensorDecomposition_left
            (K := K) (L := L) vK hvK z w) := by
  classical
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Free vK.Completion w.1.Completion :=
    fun w ↦ Module.Free.of_divisionRing
      vK.Completion w.1.Completion
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w ↦ completionModuleFinite vK hvK w
  let e :=
    completionTensorDecomposition_left
      (K := K) (L := L) vK hvK
  calc
    _root_.Algebra.norm vK.Completion z =
        _root_.Algebra.norm vK.Completion (e z) :=
      (_root_.Algebra.norm_eq_of_algEquiv e z).symm
    _ = ∏ w : AbsoluteValueExtension vK L,
        _root_.Algebra.norm vK.Completion (e z w) :=
      algebra_norm_pi_apply
        (R := vK.Completion)
        (fun w : AbsoluteValueExtension vK L ↦
          w.1.Completion) (e z)

/-- The unit-valued version of `localNorm_eq_prod`, which is the formula
used for local components of ideles. -/
theorem localNorm_units_eq_prod
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (z : (vK.Completion ⊗[K] L)ˣ) :
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w ↦ completionModuleFinite vK hvK w
    ((Units.map (_root_.Algebra.norm vK.Completion) z :
        vK.Completionˣ) : vK.Completion) =
      ∏ w : AbsoluteValueExtension vK L,
        _root_.Algebra.norm vK.Completion
          (completionTensorDecomposition_left
            (K := K) (L := L) vK hvK (z : _) w) := by
  exact localNorm_eq_prod vK hvK (z : vK.Completion ⊗[K] L)

end RelativeIdeleGroup

end
