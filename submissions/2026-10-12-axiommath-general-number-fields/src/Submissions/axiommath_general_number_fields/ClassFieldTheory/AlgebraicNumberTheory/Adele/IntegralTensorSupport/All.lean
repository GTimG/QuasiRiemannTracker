/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Adele/IntegralTensorSupport/All.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.AbsoluteValue
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.FinitePlaceCompletion
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.IdeleSupport
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Lattice
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.LocalTensorDecomposition
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Localization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# Integral support for relative adelic tensor products

Public aggregate for the lattice, localization, local tensor decomposition,
and finite-support results controlling integral relative ideles.
-/
