/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ValuedFieldTheory/Valuation/Henselian/SimpleRootFactorization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ValuedFieldTheory.Valuation.Henselian.CoprimeFactorLifting
public import Submissions.gao_general_number_fields_9672.ValuedFieldTheory.Valuation.Henselian.ValuationExtensionCriterion

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# From simple-root Hensel lifting to valuation factorization

The Henselian ring assumption now supplies the actual coprime factors.
The valuation factorization criterion then extends the monic result to
all primitive polynomials, with the prescribed reductions and degree bounds.
-/

namespace DiscreteValuationField

open ValuationTheory.DiscreteValuationField

variable {K : Type*} [Field K] (V : ValuationSubring K)
  [HenselianRing V (IsLocalRing.maximalIdeal V)]

/-- The simple-root Henselian condition supplies monic coprime-factor lifting. -/
theorem monicResidualCoprimeFactorLifting_of_henselianRing :
    MonicResidualCoprimeFactorLifting V := by
  intro f gbar hbar hf hgbar hhbar hfac hcop
  obtain ⟨g, h, hg, hh, hgh, _, _, hgmap, hhmap, _⟩ :=
    ValuationTheory.Henselian.exists_coprime_factor_lift
      (I := IsLocalRing.maximalIdeal V) f gbar hbar hf hgbar hhbar hfac hcop
  exact ⟨g, h, hg, hh, hgh, hgmap, hhmap⟩

/-- A Henselian valuation ring satisfies the full primitive factorization
form of Hensel's lemma, without completeness or rank assumptions. -/
theorem henselFactorization_of_henselianRing : HenselFactorizationProperty V :=
  henselianValuationExtension V (monicResidualCoprimeFactorLifting_of_henselianRing V)

end DiscreteValuationField
