/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/KroneckerWeber/Core.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KroneckerWeber.LocalCyclotomicEmbedding
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KroneckerWeber.RationalCyclotomicArithmeticReciprocity
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KroneckerWeber.Final
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KroneckerWeber.GlobalCompositumCyclotomicTarget
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KroneckerWeber.GlobalCompositumGlobalEmbedding
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KroneckerWeber.GlobalCompositumLeftFactors
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KroneckerWeber.GlobalCompositumLocalizationEmbedding
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KroneckerWeber.GlobalCompositumValuationInertiaBound
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KroneckerWeber.GlobalCompositumValuedEmbedding
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KroneckerWeber.GlobalPadicPrimePowInertiaBound
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KroneckerWeber.RationalRayClassFieldCyclotomic
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KroneckerWeber.RayClassComparison
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KroneckerWeber.Setup
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KroneckerWeber.UnramifiedCompositumSupport

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
















set_option autoImplicit false

/-!
# Kronecker--Weber

The reader-facing entry point for the local and global Kronecker--Weber
theorems.  Importing this module exposes both supported endpoints.
-/

/-!
# The global Kronecker--Weber theorem

Every finite abelian extension of `ℚ` is contained in a cyclotomic field.
The arithmetic construction and global degree estimate are kept in the
semantic support modules under `KroneckerWeber.Global`; this root exposes the
canonical theorem statement.
-/

noncomputable section

namespace KroneckerWeber

/-- **Global Kronecker--Weber.**

Every finite abelian extension of `ℚ` embeds in `ℚ(ζₙ)` for some positive
integer `n`.  Here `CyclotomicField n ℚ` is the concrete model of
`ℚ(ζₙ)`. -/
theorem exists_cyclotomicEmbedding
    (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) :=
  ⟨kroneckerWeberConductorCandidate (L := L),
    kroneckerWeberConductorCandidate_pos (L := L),
    ⟨kroneckerWeberCyclotomicEmbedding (L := L)⟩⟩

end KroneckerWeber

end
