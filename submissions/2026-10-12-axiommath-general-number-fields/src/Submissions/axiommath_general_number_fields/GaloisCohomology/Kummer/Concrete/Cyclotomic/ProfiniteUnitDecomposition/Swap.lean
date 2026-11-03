/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/Swap.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Gather

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Compiled final swap stage of the profinite-unit decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open ClassFormation

/-- Swap the collected free and finite coordinates. -/
noncomputable def freeFiniteSwap :
    CyclotomicFinitePart × Multiplicative ZHat ≃ₜ*
      Multiplicative ZHat × CyclotomicFinitePart :=
  LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.continuousMulEquivProdComm
    CyclotomicFinitePart (Multiplicative ZHat)

end KummerTheory.ProfiniteUnitDecomposition.Internal

end
