/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Idele/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.BaseChange
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.FiniteMathlibTopologyComparison
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdentityComponent
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormCore
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.PositiveArchimedeanSection
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.Principal
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalTopology
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.RestrictedProductUnitsTopology
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.SufficientlyLarge
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.Topology

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




























set_option autoImplicit false

/-!
# Ideles and idele classes

Public aggregate for the idele group and the idele class group of a number
field.
-/
