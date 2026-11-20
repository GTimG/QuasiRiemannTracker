/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Ramification/All.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Ramification.DegreeFromChosenPrimes
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Ramification.DegreeProduct
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Ramification.FiniteRamifiedPrimes
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Ramification.RationalPrime
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Ramification.UnramifiedRationals

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# Ramification of number fields

Public aggregate for finite ramification support, rational prime ideals,
everywhere-unramified rational extensions, and global degree bounds.
-/
