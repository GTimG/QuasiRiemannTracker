/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Galois/MathlibAbsoluteAbelianization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Infinite.TopologicalAbelianizationCongr
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Submissions.gao_general_number_fields_9686.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Comparison with Mathlib's absolute Galois abelianization

Restriction from the algebraic closure to the separable closure identifies
Mathlib's absolute Galois group with the separable-closure model. The induced
map on topological abelianizations is a homeomorphism of groups, not merely
an abstract group isomorphism.
-/

noncomputable section

universe u

/-- Mathlib's absolute Galois abelianization and the separable-closure
topological abelianization are canonically isomorphic as topological groups. -/
noncomputable def absoluteGaloisGroupAbelianizationEquivSeparable
    (K : Type u) [Field K] :
    Field.absoluteGaloisGroupAbelianization K ≃ₜ*
      TopologicalAbelianization Gal(SeparableClosure K / K) :=
  LocalClassFieldTheory.topologicalAbelianizationCongr
    (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv K)

/-- The comparison sends an absolute Galois automorphism to its restriction
to the separable closure, also after passing to the abelianization. -/
@[simp]
theorem absoluteGaloisGroupAbelianizationEquivSeparable_mk
    (K : Type u) [Field K] (σ : Field.absoluteGaloisGroup K) :
    absoluteGaloisGroupAbelianizationEquivSeparable K
        (QuotientGroup.mk σ) =
      QuotientGroup.mk (AlgEquiv.separableClosure σ) :=
  LocalClassFieldTheory.topologicalAbelianizationCongr_mk
    (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv K) σ

end
