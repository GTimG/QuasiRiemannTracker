/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Degree.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldOriginalField
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidue

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Degree of a closed finite-index class field

This leaf derives the degree of the selected class field from its exact
idèle-class norm range.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable {K : Type} [Field K] [NumberField K]

/-- The degree of the selected class field over the original number
field is the index of its defining idèle-class subgroup. -/
theorem closedFiniteIndexClassField_finrank_eq_index
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Module.finrank K
        (closedFiniteIndexClassField
          (K := K) H hclosed) =
      H.index := by
  calc
    Module.finrank K
        (closedFiniteIndexClassField
          (K := K) H hclosed) =
        (_root_.ideleClassNorm K
          (closedFiniteIndexClassField
            (K := K) H hclosed)).range.index :=
      (ideleClassNorm_index_eq_finrank_abelian K
        (closedFiniteIndexClassField
          (K := K) H hclosed)).symm
    _ = H.index :=
      congrArg Subgroup.index
        (closedFiniteIndexClassField_ideleClassNorm_range
          (K := K) H hclosed)

end GlobalClassFields
end GlobalClassFieldTheory

end
