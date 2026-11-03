/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.EmbeddingNorm
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisDescent
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisNorm
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdealClass
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleClassBaseChange
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.InfiniteOnePlaceBaseNorm
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalNorm
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormLocalOrder
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormProperties
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.OnePlaceBaseNorm

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

















set_option autoImplicit false

/-!
# Ideles in finite extensions of number fields

Public aggregate for base change, extension, and norm maps on ideles and
idele classes.
-/
