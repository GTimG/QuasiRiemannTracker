/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldUnique.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Uniqueness of the small Hilbert class field inside a separable closure

The maximality condition determines an actual intermediate field, not merely
an isomorphism class.  It does not distinguish a unique field automorphism.
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- Two small Hilbert class fields inside the same separable closure are
equal as intermediate fields. -/
theorem smallHilbertClassFields_eq
    (K : Type u) [Field K] [NumberField K]
    (E F : FiniteAbelianExtension K)
    (hE : IsSmallHilbertClassField E)
    (hF : IsSmallHilbertClassField F) :
    E.1 = F.1 := by
  have hEF : E.1 ≤ F.1 := by
    obtain ⟨f⟩ := hF.2 E hE.1
    let σ : E →ₐ[K] SeparableClosure K := F.1.val.comp f
    have hσ : σ.fieldRange = E.1 := AlgHom.fieldRange_of_normal σ
    rw [← hσ]
    intro x hx
    obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    exact (f y).property
  have hFE : F.1 ≤ E.1 := by
    obtain ⟨f⟩ := hE.2 F hF.1
    let σ : F →ₐ[K] SeparableClosure K := E.1.val.comp f
    have hσ : σ.fieldRange = F.1 := AlgHom.fieldRange_of_normal σ
    rw [← hσ]
    intro x hx
    obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    exact (f y).property
  exact le_antisymm hEF hFE

end ClassFieldTheory

end
