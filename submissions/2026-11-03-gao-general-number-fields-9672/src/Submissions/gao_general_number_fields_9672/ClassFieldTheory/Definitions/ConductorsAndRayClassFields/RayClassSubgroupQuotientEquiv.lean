/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/RayClassSubgroupQuotientEquiv.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The quotient induced by a ray-class Artin map

The prescribed subgroup is identified with the Artin kernel before applying
the first isomorphism theorem.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

/-- The isomorphism induced by the Artin map of a ray-class realization. -/
def rayClassSubgroupQuotientEquiv
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m))
    (R : RayClassSubgroupRealization K m H) :
    (RayClassGroup m ⧸ H) ≃* (R.extension ≃ₐ[K] R.extension) :=
  (QuotientGroup.quotientMulEquivOfEq R.artin_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      R.artin R.artin_surjective)

end ClassFieldTheory

end
