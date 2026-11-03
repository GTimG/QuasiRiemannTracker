/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LubinTate/Padic/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerCoefficient
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.All
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardCompositum
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFixedField
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFrobenius
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardResidue
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardUnramified
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerFixedField
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerPrimitive
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerThetaFixed
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusEvaluation
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusLift
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedLevel
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveAction
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveIrreducible
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveUniformizer
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedResidueFrobenius
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedStandardLevelTransport
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedField
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedFrobeniusFixed
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.All
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.MultiplicativeIntertwiner
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.Padic.MultiplicativeSeries

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
