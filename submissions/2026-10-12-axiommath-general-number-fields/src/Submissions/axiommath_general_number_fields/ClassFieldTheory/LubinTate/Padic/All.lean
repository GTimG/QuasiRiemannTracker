/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LubinTate/Padic/All.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerCoefficient
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardCompositum
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFixedField
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFrobenius
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardResidue
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardUnramified
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerFixedField
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerPrimitive
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerThetaFixed
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusEvaluation
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusLift
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedLevel
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveAction
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveIrreducible
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveUniformizer
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedResidueFrobenius
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedStandardLevelTransport
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedField
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedFrobeniusFixed
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.MultiplicativeIntertwiner
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.Padic.MultiplicativeSeries

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

























set_option autoImplicit false

/-!
# P-adic Lubin--Tate theory

Aggregate for the multiplicative Lubin--Tate series and its completed-level,
Frobenius, residue, fixed-field, and changed-uniformizer constructions.
-/
