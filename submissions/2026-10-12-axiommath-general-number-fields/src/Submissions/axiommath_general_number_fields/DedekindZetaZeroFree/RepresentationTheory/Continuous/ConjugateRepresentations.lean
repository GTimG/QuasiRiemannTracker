/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Continuous/ConjugateRepresentations.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Analysis.InnerProductSpaces.OperatorConjugation
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.RepresentationTheory.Continuous.MatrixCoefficients

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Continuous/Conjugate.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open scoped InnerProductSpace

namespace DedekindZetaZeroFree.TauCeti

namespace ContRepresentation

variable {𝕜 ι G V : Type*} [RCLike 𝕜] [Fintype ι] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (e : OrthonormalBasis ι 𝕜 V)

noncomputable def conjugate (π : ContRepresentation 𝕜 G V) : ContRepresentation 𝕜 G V :=
  .ofMonoidHom
    { toFun g := conjCLM e (π g)
      map_one' := by simp
      map_mul' g h := by rw [map_mul, conjCLM_mul] }

variable (π : ContRepresentation 𝕜 G V)

omit [TopologicalSpace G] in

@[simp]
theorem conjugate_apply (g : G) : conjugate e π g = conjCLM e (π g) :=
  (rfl)

omit [TopologicalSpace G] in

@[simp]
theorem conjugate_conjugate : conjugate e (conjugate e π) = π :=
  DFunLike.ext _ _ fun g ↦ by simp

theorem continuous_conjugate (hπ : Continuous π) : Continuous (conjugate e π) :=
  (lipschitzWith_one_conjCLM e).continuous.comp hπ

theorem star_matrixCoeff_eq_matrixCoeff_conjugate (hπ : Continuous π) (v w : V) :
    star (matrixCoeff π hπ v w) =
      matrixCoeff (conjugate e π) (continuous_conjugate e π hπ)
        (conjugation e v) (conjugation e w) := by
  ext g
  simp [inner_conjugation_conjugation, RCLike.star_def]

end ContRepresentation

end DedekindZetaZeroFree.TauCeti
