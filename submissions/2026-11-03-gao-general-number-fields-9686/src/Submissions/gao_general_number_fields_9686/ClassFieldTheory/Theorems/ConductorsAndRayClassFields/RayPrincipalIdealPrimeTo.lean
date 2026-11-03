/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayPrincipalIdealPrimeTo.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayPrincipalIdealSubgroup
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayPrincipalIdealMembership
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Ray-principal ideals are prime to the modulus

The local congruence condition makes the corresponding principal idèle
integral-unit-valued at every finite prime in the modulus support.
-/

open scoped Classical NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

universe u

/-- A ray-principal fractional ideal has zero exponent at every finite
prime in the modulus support. -/
theorem rayPrincipalIdealSubgroup_le_primeToIdeals
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) :
    rayPrincipalIdealSubgroup m ≤ rayClassPrimeToIdeals m := by
  intro I hI
  obtain ⟨x, hx, hIx⟩ := (mem_rayPrincipalIdealSubgroup_iff m I).1 hI
  intro v hv
  rw [← hIx, ← IdeleGroup.fractionalIdeal_principalIdele]
  change FractionalIdeal.count K v
      (((FractionalIdealGroup.factorization (K := K))
        (FiniteIdeleGroup.valuationVector
          (IdeleGroup.principalIdele K x).2) : FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
  rw [FractionalIdealGroup.count_factorization,
    FiniteIdeleGroup.valuationVector_apply]
  apply (FiniteIdeleGroup.localOrder_eq_zero_iff v
    ((IdeleGroup.principalIdele K x).2 v)).2
  apply RayClass.localHigherUnitGroup_le_integralUnits v (m.finitePart v)
  exact hx.1 v hv

end ClassFieldTheory

end
