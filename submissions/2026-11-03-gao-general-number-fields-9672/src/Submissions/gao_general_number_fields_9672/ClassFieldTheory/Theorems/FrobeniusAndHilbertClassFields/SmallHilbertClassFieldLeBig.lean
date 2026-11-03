/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldLeBig.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The small Hilbert class field is a subfield of the big one

The extensions are intermediate fields of one separable closure, so the
result is literal containment, not only an abstract embedding.
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- Every small Hilbert class field is contained in every big Hilbert class
field inside the fixed separable closure. -/
theorem smallHilbertClassField_le_big
    (K : Type u) [Field K] [NumberField K]
    (E F : FiniteAbelianExtension K)
    (hE : IsSmallHilbertClassField E)
    (hF : IsBigHilbertClassField F) :
    E.1 ≤ F.1 := by
  obtain ⟨f⟩ := hF.2 E hE.1.1
  let σ : E →ₐ[K] SeparableClosure K := F.1.val.comp f
  have hσ : σ.fieldRange = E.1 := AlgHom.fieldRange_of_normal σ
  rw [← hσ]
  intro x hx
  obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
  exact (f y).property

end ClassFieldTheory

end
