/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/FreeCoordinate.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.CyclotomicQuotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Local coordinates of the profinite-unit decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation
open LocalFieldTheory.Padic

/-- The `p`-adic coordinate of the global free factor in
`zHatUnitsDecomposition` is exactly the free factor in the genuine
local decomposition of the `p`-adic unit coordinate. -/
@[simp]
theorem zHatUnitsDecomposition_freeCoordinate
    (u : ZHatˣ) (p : Nat.Primes) :
    zHatToPadicInt p
        (Multiplicative.toAdd
          (zHatUnitsDecomposition u).1) =
      Multiplicative.toAdd
        (((padicUnitDecomposition p.1).symm
          (zHatUnitsContinuousMulEquivPrimeProduct u p)).2) := by
  let y : ProfiniteIntegerPrimeProduct :=
    fun q =>
      Multiplicative.toAdd
        (((padicUnitDecomposition q.1).symm
          (zHatUnitsContinuousMulEquivPrimeProduct u q)).2)
  change
    zHatToPadicInt p
        (zHatContinuousAddEquivPrimeProduct.symm y) =
      y p
  exact
    congrFun
      (zHatContinuousAddEquivPrimeProduct.apply_symm_apply y) p

end KummerTheory

end
