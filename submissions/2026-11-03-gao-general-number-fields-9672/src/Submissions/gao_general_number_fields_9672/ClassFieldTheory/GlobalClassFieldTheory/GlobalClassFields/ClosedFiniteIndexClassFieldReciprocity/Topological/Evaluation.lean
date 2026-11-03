/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Topological/Evaluation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Evaluation of continuous closed finite-index reciprocity

The public theorem uses the named reducible value provider and specializes
the generic transported-reciprocity calculation.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

variable {K : Type} [Field K] [NumberField K]

/-- Evaluation of the selected class-field equivalence is the named inverse
global norm-residue value in the quotient by the defining subgroup. -/
@[simp]
theorem
    closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient_apply
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (σ : Gal((closedFiniteIndexClassField
      (K := K) H hclosed) / K)) :
    closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient
        (K := K) H hclosed σ =
      closedFiniteIndexClassFieldReciprocityValue
        (K := K) H hclosed σ :=
  globalReciprocityContinuousMulEquiv_trans_quotientOfEq_apply
    H
    (closedFiniteIndexClassField_ideleClassNorm_range
      (K := K) H hclosed)
    σ

end GlobalClassFields
end GlobalClassFieldTheory

end
