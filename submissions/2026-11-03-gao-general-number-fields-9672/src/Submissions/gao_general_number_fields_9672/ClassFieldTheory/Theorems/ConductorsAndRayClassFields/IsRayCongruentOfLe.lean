/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/IsRayCongruentOfLe.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsRayCongruent
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayLocalHigherUnitAntitone

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Ray congruence under enlargement of the modulus

A larger modulus has at least as strong a congruence condition at each
finite prime and at least as many real positivity conditions.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory.IsRayCongruent

universe u

open NumberField IsDedekindDomain

/-- An element ray-congruent for a larger modulus is ray-congruent for a
smaller modulus. -/
theorem of_le
    {K : Type u} [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n)
    {x : Kˣ} (hx : IsRayCongruent n x) :
    IsRayCongruent m x := by
  constructor
  · intro v hv
    have hvn : v ∈ n.finitePart.support := by
      apply Finsupp.mem_support_iff.mpr
      have hpos : 0 < m.finitePart v :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
      exact Nat.ne_of_gt (lt_of_lt_of_le hpos (hmn.1 v))
    exact rayLocalHigherUnitGroup_antitone v (hmn.1 v) (hx.1 v hvn)
  · intro v hv
    exact hx.2 v (hmn.2 hv)

end ClassFieldTheory.IsRayCongruent

end
