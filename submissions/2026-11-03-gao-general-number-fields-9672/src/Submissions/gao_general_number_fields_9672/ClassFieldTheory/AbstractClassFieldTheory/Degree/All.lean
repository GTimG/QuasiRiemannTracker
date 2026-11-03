/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AbstractClassFieldTheory/Degree/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormConjugation
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Degree.PadicCyclicClosure
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Degree.ProfiniteIntegerFiniteQuotient
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/















set_option autoImplicit false

/-!
# Degree and valuation data

Focused aggregate for abstract fields, normalized degrees, Frobenius, norms, prime elements, and
valuation laws used by class formations.
-/
