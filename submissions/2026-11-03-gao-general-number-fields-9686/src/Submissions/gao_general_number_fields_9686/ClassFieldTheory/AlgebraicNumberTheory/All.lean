/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Adele.All
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Completion.All
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.CompositumEmbedding
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.FiniteAbelianCompositum
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Galois.All
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.All
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceAdicCompletionCongrEquiv
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivTopology
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.NumberField.All
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.All
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.QuadraticReciprocity
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Ramification.All
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.RayClass.All
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.SUnit.All
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.TensorProduct

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




















set_option autoImplicit false

/-!
# Algebraic number theory

Public root for the reusable global algebraic-number-theory layer used by
class field theory. It exports finite abelian composita, idèles and idèle
classes in extensions, normal-closure and splitting results, ray class groups,
S-units, and the ramification and degree results needed by global applications.
-/
