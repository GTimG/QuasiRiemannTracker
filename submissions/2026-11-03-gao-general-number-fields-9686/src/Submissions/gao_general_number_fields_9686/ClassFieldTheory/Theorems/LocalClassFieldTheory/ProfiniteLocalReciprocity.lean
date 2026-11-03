/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/LocalClassFieldTheory/ProfiniteLocalReciprocity.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.LocalClassFieldTheory.TopologicalProfiniteCompletion
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteLocalReciprocity
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.LocalField.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Profinite local reciprocity

For a nonarchimedean local field `K`, the profinite completion of `Kˣ` with
respect to its open finite-index normal subgroups is continuously
multiplicatively equivalent to the topological abelianization of Mathlib's
absolute Galois group of `K`.
-/

noncomputable section

namespace ClassFieldTheory

/-- **Profinite local reciprocity.** The topological profinite completion of
the multiplicative group of a nonarchimedean local field is continuously
multiplicatively equivalent to its absolute Galois abelianization. -/
theorem profiniteLocalReciprocity
    (K : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Nonempty
      (LocalClassFieldTheory.TopologicalProfiniteCompletion Kˣ ≃ₜ*
        _root_.Field.absoluteGaloisGroupAbelianization K) := by
  exact ⟨LocalClassFieldTheory.profiniteLocalReciprocity K⟩

end ClassFieldTheory

end
