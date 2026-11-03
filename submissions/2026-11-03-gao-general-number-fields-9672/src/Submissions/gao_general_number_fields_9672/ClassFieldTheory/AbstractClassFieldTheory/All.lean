/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AbstractClassFieldTheory/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Degree.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.All

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Abstract class field theory

Public root for abstract degree data, class formations, reciprocity, and the construction and
naturality of Artin maps. The public declarations live in the `ClassFormation` namespace. This
library is independent of local class field theory.

The representation-free degree, field, extension, and topological-generation
APIs are universe-polymorphic.  The boundary that uses Mathlib's `Rep ℤ G` is
necessarily universe zero because `Rep` currently places its coefficient ring
and acting group in the same universe; the affected source sections state that
constraint explicitly.
-/
