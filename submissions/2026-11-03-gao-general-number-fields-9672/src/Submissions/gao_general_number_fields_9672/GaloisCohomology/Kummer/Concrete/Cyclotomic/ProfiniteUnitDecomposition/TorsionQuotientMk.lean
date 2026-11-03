/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/TorsionQuotientMk.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientEquiv

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Evaluation of the torsion-quotient equivalence
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation

/-- The torsion-quotient equivalence evaluates a quotient class by
taking the genuine torsion-free coordinate of the chosen product
decomposition.  This is the commuting square needed to pass between an
actual cyclotomic character and the `ZHat`-coordinate of its torsion
fixed field. -/
@[simp]
theorem torsionQuotientEquivOfZHatMulDecomposition_mk
    (G T : Type*) [CommGroup G] [CommGroup T]
    [TopologicalSpace G] [TopologicalSpace T]
    [IsTopologicalGroup G] [IsTopologicalGroup T]
    [CompactSpace G]
    (E : G ≃ₜ* Multiplicative ZHat × T)
    (hT : Dense (CommGroup.torsion T : Set T))
    (g : G) :
    torsionQuotientEquivOfZHatMulDecomposition
        G T E hT (QuotientGroup.mk g) =
      (E g).1 := by
  rfl

end KummerTheory

end
