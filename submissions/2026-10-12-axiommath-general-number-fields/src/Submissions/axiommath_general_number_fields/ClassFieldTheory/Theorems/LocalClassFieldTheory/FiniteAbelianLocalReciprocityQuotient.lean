/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocityQuotient.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormQuotient
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.MathlibInterface
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# Quotient form of finite abelian local reciprocity

This module states the quotient formulation of local reciprocity for a
finite abelian extension `L / K` of a nonarchimedean local field.  Under the
finite-dimensional, abelian-Galois, valuative, and topological assumptions,
the conclusion identifies `Kˣ / N_{L/K}(Lˣ)` with the ordinary Galois group
by a continuous multiplicative equivalence.
-/

noncomputable section

namespace ClassFieldTheory

/-- The field-norm quotient is continuously multiplicatively equivalent to
the finite abelian Galois group. -/
theorem finiteAbelianLocalReciprocity_quotient
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Nonempty
      (FieldNormQuotient K L ≃ₜ* (L ≃ₐ[K] L)) := by
  exact LocalCFT.finiteAbelianLocalReciprocity_quotient K L

end ClassFieldTheory

end
