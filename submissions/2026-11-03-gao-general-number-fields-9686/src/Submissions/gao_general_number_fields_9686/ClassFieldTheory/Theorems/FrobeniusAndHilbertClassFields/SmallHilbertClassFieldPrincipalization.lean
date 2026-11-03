/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldPrincipalization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Principalization in the small Hilbert class field

The principal ideal theorem says that extension to the Hilbert class field
makes every integral ideal of the base number field principal.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- Every integral ideal becomes principal in a small Hilbert class field. -/
theorem ideals_becomePrincipalInSmallHilbertClassField
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E) :
    ∀ I : Ideal (𝓞 K),
      (I.map (algebraMap (𝓞 K) (𝓞 E))).IsPrincipal := by
  exact GlobalClassFieldComparison.ideals_becomePrincipalInSmallHilbertClassField_of_isSmall K E hE

end ClassFieldTheory

end
