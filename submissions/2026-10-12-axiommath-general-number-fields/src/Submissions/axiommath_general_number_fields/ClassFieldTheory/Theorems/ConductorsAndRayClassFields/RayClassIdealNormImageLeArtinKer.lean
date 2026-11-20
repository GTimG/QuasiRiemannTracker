/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassIdealNormImageLeArtinKer.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealNorm
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicIdealNormArtinKernel

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Ideal norms are killed by the ray-class Artin map

This is the forward direction of the ideal-theoretic norm-kernel formula.
The subgroup is formed from actual fractional-ideal norms, not from idèle
norms. Equality requires the separate reverse approximation theorem.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- For finite abelian reciprocity data, the image of genuine ideal norms
in the ray class group lies in the normalized Artin kernel. -/
theorem rayClassIdealNormImage_le_artinKer
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    rayClassIdealNormImage K L D.modulus ≤ D.artin.ker :=
  GlobalClassFieldComparison.idealNormImage_le_finiteAbelianReciprocityArtinKer K L D

end ClassFieldTheory

end
