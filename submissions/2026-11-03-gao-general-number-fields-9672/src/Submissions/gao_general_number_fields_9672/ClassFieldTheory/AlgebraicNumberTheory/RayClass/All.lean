/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/RayClass/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Approximation
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.RayClass.IdealNorm
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.RayClass.LocalConductor
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Narrow
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.RayClass.OrdinaryClassGroupComparison
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.RayClass.PrimeGeneration
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.RayClass.PublicHigherUnitComparison
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Rational
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/














set_option autoImplicit false

/-!
# Ray class groups

Public aggregate for approximation, congruence subgroups, and ray class
groups of number fields.
-/
