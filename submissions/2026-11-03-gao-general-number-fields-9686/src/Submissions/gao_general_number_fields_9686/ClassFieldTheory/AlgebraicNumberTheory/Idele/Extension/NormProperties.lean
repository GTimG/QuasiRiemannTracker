/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/NormProperties.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Functorial properties of the idele norm

In the tensor-product presentation `𝔸_L = 𝔸_K ⊗_K L`, the idele norm is
the determinant norm of a finite free algebra.  Thus transitivity is the
general transitivity theorem for determinant norms.  The remaining
statements record the base-field power formula and compatibility with
principal ideles and Galois conjugation.
-/

open scoped BigOperators
open NumberField

noncomputable section


namespace RelativeIdeleGroup

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [NumberField K] [NumberField L] in
/-- The field norm, regarded in `L`, is the product of all Galois
conjugates.  This is the unit-valued form used for principal ideles in
the Galois product norm formula. -/
theorem fieldNormUnits_eq_prod_conjugates
    [IsGalois K L] (x : Lˣ) :
    Units.map (algebraMap K L)
        (Units.map (_root_.Algebra.norm K) x) =
      ∏ σ : L ≃ₐ[K] L,
        Units.map σ.toRingEquiv.toMonoidHom x := by
  apply Units.ext
  simp only [Units.coe_map, Units.coe_prod]
  convert
    (_root_.Algebra.norm_eq_prod_automorphisms K (x : L))
    using 1; rfl

omit [NumberField L] in
/-- On the diagonal copy of `Lˣ`, after extending the norm
back to `L`, the principal idele of the norm is the product of the
Galois-conjugate principal ideles. -/
theorem inclusion_norm_principalIdele_eq_prod_conjugates
    [IsGalois K L] (x : Lˣ) :
    inclusion K L (norm K L (principalIdele K L x)) =
      ∏ σ : L ≃ₐ[K] L,
        σ • principalIdele K L x := by
  rw [norm_principalIdele, inclusion_principalIdele]
  simp_rw [smul_principalIdele]
  rw [← map_prod]
  exact congrArg (principalIdele K L)
    (fieldNormUnits_eq_prod_conjugates K L x)

end RelativeIdeleGroup

end
