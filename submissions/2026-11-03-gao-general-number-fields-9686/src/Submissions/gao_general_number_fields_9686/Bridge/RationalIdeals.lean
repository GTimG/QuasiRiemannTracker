/-
2026-11-03 Dirichlet specialization bridge by Zhongpai Gao with AI assistance.
Apache-2.0. Original source attribution and licenses below are retained.
This module is adapted from the isolated checked RationalIdeals.lean proof:
Lean 4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
Tracker adaptation changes import paths only; all theorem bodies are unchanged.
The adapter applies to the genuine strengthened native Hecke theorem; full
native endpoint compatibility and official tracker admission remain pending.
-/
/-
Rational ideal arithmetic for the faithful Dirichlet / native Hecke bridge.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Uses Mathlib's rational ring-of-integers equivalence and ideal norm theorems.
-/
import Mathlib

open NumberField
open scoped NumberField

namespace TrackerBridge

abbrev RatIntegers := 𝓞 ℚ

noncomputable def ratIdealNat (I : Ideal RatIntegers) : ℕ :=
  Ideal.absNorm (I.map (Rat.ringOfIntegersEquiv : RatIntegers →+* ℤ))

lemma ratIdeal_span_norm_map (I : Ideal RatIntegers) :
    Ideal.span {(ratIdealNat I : RatIntegers)} = I := by
  apply (Ideal.relIsoOfBijective (Rat.ringOfIntegersEquiv : RatIntegers →+* ℤ)
    Rat.ringOfIntegersEquiv.bijective).symm.injective
  change (Ideal.span {(ratIdealNat I : RatIntegers)}).map
    (Rat.ringOfIntegersEquiv : RatIntegers →+* ℤ) = I.map _
  rw [Ideal.map_span]
  simpa only [Set.image_singleton, map_natCast, ratIdealNat] using
    Int.ideal_span_absNorm_eq_self (I.map (Rat.ringOfIntegersEquiv : RatIntegers →+* ℤ))

@[simp] lemma rat_absNorm_span (n : ℕ) :
    Ideal.absNorm (Ideal.span {(n : RatIntegers)}) = n := by
  rw [Ideal.absNorm_span_natCast]
  rw [NumberField.RingOfIntegers.rank]
  simp only [Module.finrank_self, pow_one]

lemma ratIdeal_eq_span_absNorm (I : Ideal RatIntegers) :
    Ideal.span {(Ideal.absNorm I : RatIntegers)} = I := by
  have h := ratIdeal_span_norm_map I
  have hn : Ideal.absNorm I = ratIdealNat I := by
    calc Ideal.absNorm I = Ideal.absNorm (Ideal.span {(ratIdealNat I : RatIntegers)}) := congrArg Ideal.absNorm h.symm
         _ = ratIdealNat I := rat_absNorm_span _
  simpa only [hn] using h

noncomputable def ratIdealEquivNat : Ideal RatIntegers ≃ ℕ where
  toFun := Ideal.absNorm
  invFun := fun n => Ideal.span {(n : RatIntegers)}
  left_inv := ratIdeal_eq_span_absNorm
  right_inv := rat_absNorm_span

lemma rat_span_sup_span_iff (n q : ℕ) :
    Ideal.span {(n : RatIntegers)} ⊔ Ideal.span {(q : RatIntegers)} = ⊤ ↔
      n.Coprime q := by
  rw [Ideal.sup_eq_top_iff_isCoprime]
  constructor
  · intro h
    apply Nat.isCoprime_iff_coprime.mp
    simpa only [map_natCast] using h.map (Rat.ringOfIntegersEquiv : RatIntegers →+* ℤ)
  · intro h
    exact h.cast

lemma rat_ideal_coprime_iff (I : Ideal RatIntegers) (q : ℕ) :
    I ⊔ Ideal.span {(q : RatIntegers)} = ⊤ ↔ (Ideal.absNorm I).Coprime q := by
  conv_lhs => rw [← ratIdeal_eq_span_absNorm I]
  exact rat_span_sup_span_iff _ _

end TrackerBridge
