/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HasseArf/LowerRamificationGroupAntitone.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HasseArf.LowerRamificationGroup

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# The lower ramification filtration decreases

The definition uses powers of the maximal ideal of a valuation subring.
The inclusion below holds without local-field or finiteness hypotheses.
-/

namespace ClassFieldTheory

universe u v

/-- A larger lower index gives a smaller ramification subgroup. -/
theorem lowerRamificationGroup_antitone
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    Antitone (lowerRamificationGroup K A) := by
  intro m n hmn σ hσ x
  exact (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal A)
    (Nat.add_le_add_right hmn 1)) (hσ x)

end ClassFieldTheory
