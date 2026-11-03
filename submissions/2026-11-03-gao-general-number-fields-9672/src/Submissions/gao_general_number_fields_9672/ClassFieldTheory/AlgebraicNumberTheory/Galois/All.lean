/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Galois/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Galois.CyclicPrimeDegreeSubextension
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Galois.CyclicPrimeSubextension
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Galois.FixedFieldLattice
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Galois.InfiniteBaseChange
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteAbelianization
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteGaloisBaseEquiv
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Galois.MaximalAbelianSubextension
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Galois.NormalFieldRange
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Galois.RelativeAbelianization
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Galois.UnboundedDegree

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/













set_option autoImplicit false

/-! # Galois subextensions and fixed-field constructions -/
