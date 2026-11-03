/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivAdeleTopology
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivFiniteIntegral
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivIdeleClassTopology
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivTopology
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.BaseChange
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.ConnectedComponentQuotientCongr
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.InfiniteAlgEquiv
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibComparison
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormalClosureNorm
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


















set_option autoImplicit false

/-!
# Idelic class groups

Public aggregate for the ordinary ideal class quotient of the ideles and its
base-change, norm-comparison, tower, and algebra-equivalence constructions.
-/
