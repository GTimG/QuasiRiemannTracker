/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Topological/QuotientTransport.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Continuous transport between equal quotient groups

Equality of normal subgroups identifies their quotient groups with the same
native quotient topology.  Eliminating the equality therefore gives the
continuous multiplicative equivalence directly; no discrete-topology
instances or domain-specific class-field tower are required.
-/

noncomputable section

namespace QuotientGroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Equal normal subgroups induce a continuous multiplicative equivalence
between their quotient groups with their native quotient topologies. -/
noncomputable def quotientContinuousMulEquivOfEq
    {N H : Subgroup G} [N.Normal] [H.Normal]
    (h : N = H) :
    G ⧸ N ≃ₜ* G ⧸ H := by
  subst H
  exact ContinuousMulEquiv.refl _

/-- Forgetting topology from `quotientContinuousMulEquivOfEq` recovers the
canonical multiplicative equivalence induced by the same equality. -/
@[simp]
theorem quotientContinuousMulEquivOfEq_apply
    {N H : Subgroup G} [N.Normal] [H.Normal]
    (h : N = H) (x : G ⧸ N) :
    quotientContinuousMulEquivOfEq h x =
      QuotientGroup.quotientMulEquivOfEq h x := by
  subst H
  refine QuotientGroup.induction_on x ?_
  intro g
  exact
    (QuotientGroup.quotientMulEquivOfEq_mk
      (G := G) (M := N) (N := N) rfl g).symm

end QuotientGroup

end
