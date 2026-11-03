/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LocalClassFieldTheory/Infinite/All.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtin
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtinRestriction
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteFiniteQuotientTransitions
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteFiniteQuotients
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteGaloisAbelianization
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbstractProfiniteCompletionComparison
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Infinite.FiniteAbelianQuotientKernels
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Infinite.FiniteReciprocityDiagram
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Infinite.LocalMultiplicativeCompletion
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletion
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletionCriteria
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteLocalReciprocity
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Infinite.TopologicalAbelianizationCongr

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/















set_option autoImplicit false

/-!
# Infinite local class field theory

Public aggregate for the topological profinite completion, compatible finite
Artin maps, the absolute local Artin map, and the profinite local reciprocity
equivalence.
-/
