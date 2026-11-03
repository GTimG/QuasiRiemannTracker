/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/CyclotomicQuotient.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientMk

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# The cyclotomic profinite-unit torsion quotient
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation

/-- Cyclotomic-character form of the torsion decomposition: quotienting `ℤ̂ˣ` by
the closure of its torsion subgroup leaves one copy of `ℤ̂`. -/
noncomputable def zHatUnitsTorsionQuotientEquiv :
    ZHatˣ ⧸ (CommGroup.torsion ZHatˣ).topologicalClosure ≃ₜ*
      Multiplicative ZHat :=
  torsionQuotientEquivOfZHatMulDecomposition
    ZHatˣ CyclotomicFinitePart
      zHatUnitsDecomposition
        dense_torsion_cyclotomicFinitePart

end KummerTheory

end
