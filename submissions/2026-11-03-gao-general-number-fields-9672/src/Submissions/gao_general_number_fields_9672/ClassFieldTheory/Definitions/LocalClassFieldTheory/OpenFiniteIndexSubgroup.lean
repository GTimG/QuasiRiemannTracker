/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/LocalClassFieldTheory/OpenFiniteIndexSubgroup.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Units

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Open finite-index subgroups of a field's multiplicative group
-/

namespace ClassFieldTheory

universe u

/-- An open finite-index subgroup of the multiplicative group `Kˣ`.  The
inherited order is ordinary subgroup inclusion. -/
abbrev OpenFiniteIndexSubgroup
    (K : Type u) [Field K] [TopologicalSpace K] :=
  { H : Subgroup Kˣ // IsOpen (H : Set Kˣ) ∧ H.FiniteIndex }

end ClassFieldTheory
