/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/IdeleClassPowerLocalUnitQuotient/FinitePlaceCompletionInstances.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import Submissions.gao_general_number_fields_9686.ValuedFieldTheory.Valuation.ValuedAdicComplete
public import Mathlib.NumberTheory.NumberField.ProductFormula

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Canonical structures on finite completions

This module installs the complete discrete valuation, characteristic-zero,
and finite residue-field structures used by finite-place class-field
arithmetic.
-/

open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The distinguished valuation on a finite completion of a number field is
complete discrete. -/
noncomputable instance finitePlaceAdicCompletion_isCompleteDiscrete
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
      (Valued.v :
        Valuation (v₀.adicCompletion K)
          (WithZero (Multiplicative ℤ))) where
  isRankOneDiscrete := inferInstance
  isAdicComplete :=
    ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdicComplete

/-- A finite completion of a number field has characteristic zero. -/
noncomputable instance finitePlaceAdicCompletion_charZero
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    CharZero (v₀.adicCompletion K) :=
  charZero_of_injective_algebraMap
    (algebraMap K (v₀.adicCompletion K)).injective

/-- The residue field of a finite completion of a number field is finite. -/
noncomputable instance finitePlaceAdicCompletion_residueFinite
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    Finite
      (IsLocalRing.ResidueField
        (Valued.v :
          Valuation (v₀.adicCompletion K)
            (WithZero (Multiplicative ℤ))).valuationSubring) := by
  change Finite (Valued.ResidueField (v₀.adicCompletion K))
  exact _root_.finite_adicCompletion_residueField K v₀

end GlobalClassFieldTheory.ClassFieldAxiom

end
