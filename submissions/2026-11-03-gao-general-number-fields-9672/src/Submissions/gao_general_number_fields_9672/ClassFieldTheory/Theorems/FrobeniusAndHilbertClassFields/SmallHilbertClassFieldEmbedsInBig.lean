/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldEmbedsInBig.lean
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
# Inclusion of the small Hilbert class field in the big one

Everywhere-unramified extensions are unramified at finite places, so the
maximality property of a big Hilbert class field supplies the embedding.
-/

namespace ClassFieldTheory

universe u

/-- Every small Hilbert class field embeds over the base into every big
Hilbert class field. -/
theorem smallHilbertClassField_embedsInBig
    (K : Type u) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E)
    (F : FiniteAbelianExtension K) (hF : IsBigHilbertClassField F) :
    Nonempty (E →ₐ[K] F) :=
  hF.2 E hE.1.1

end ClassFieldTheory
