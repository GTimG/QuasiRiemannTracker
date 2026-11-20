/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ValuedFieldTheory/Valuation/Henselian/AlgebraicExtensionUniqueness.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ValuedFieldTheory.Valuation.Henselian.AlgebraicIntegralClosure
public import Submissions.axiommath_general_number_fields.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Uniqueness over an algebraic extension of a Henselian valued field

The integral closure is an actual valuation ring. Every extension valuation
has this ring of integers, so any two extension valuations are equivalent.
-/

namespace ValuationTheory.Henselian

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  (V : ValuationSubring K) [HenselianRing V (IsLocalRing.maximalIdeal V)]

/-- The valuation ring of any algebraic extension valuation is the actual
integral closure of the Henselian base valuation ring. -/
theorem valuationSubring_eq_integralClosure_of_henselianRing
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : _root_.Valuation L Γ) [V.valuation.HasExtension w] :
    w.valuationSubring.toSubring = (integralClosure V L).toSubring := by
  have hval : ∀ z : L,
      z ∈ (integralClosure V.valuation.valuationSubring L).toSubring ∨
      z⁻¹ ∈ (integralClosure V.valuation.valuationSubring L).toSubring := by
    rw [ValuationSubring.valuationSubring_valuation]
    exact integralClosure_mem_or_inv_of_henselianRing (L := L) V
  have h := congrArg ValuationSubring.toSubring
    (_root_.DiscreteValuationField.Valuation.normFormula_extension_valuationSubring_eq_integralClosure_of_mem_or_inv
      V hval w)
  change w.valuationSubring.toSubring =
    (integralClosure V.valuation.valuationSubring L).toSubring at h
  rw [ValuationSubring.valuationSubring_valuation] at h
  exact h

/-- Extension valuations over a Henselian base have the same valuation ring. -/
theorem valuationSubring_eq_of_henselianRing
    {Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₁]
    [LinearOrderedCommGroupWithZero Γ₂]
    (w₁ : _root_.Valuation L Γ₁) (w₂ : _root_.Valuation L Γ₂)
    [V.valuation.HasExtension w₁] [V.valuation.HasExtension w₂] :
    w₁.valuationSubring = w₂.valuationSubring := by
  have h := (valuationSubring_eq_integralClosure_of_henselianRing V w₁).trans
    (valuationSubring_eq_integralClosure_of_henselianRing V w₂).symm
  exact SetLike.ext (fun z => SetLike.ext_iff.mp h z)

end ValuationTheory.Henselian
