/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.SignedCenterSeries

/-! Actual finite exceptional valuation choices and the infinite good-prime
monomial expansion are combined before defining the two extracted ideal scales.
-/
set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

abbrev BadIndex (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) :=
  (P : bad) → allowed P.val

def badSeriesTerm (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (s₁ s₂ : ℂ) (k : BadIndex bad allowed) : ℂ :=
  ∏ P : bad,(eulerVariable ψ₁ P.val s₁)^(k P).val.1*
    (eulerVariable ψ₂ P.val s₂)^(k P).val.2

lemma badSeries_expansion (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (s₁ s₂ : ℂ) :
    exceptionalProduct ψ₁ ψ₂ bad allowed s₁ s₂=
      ∑ k : BadIndex bad allowed,badSeriesTerm ψ₁ ψ₂ bad allowed s₁ s₂ k := by
  unfold exceptionalProduct exceptionalLocal
  rw [←Finset.prod_coe_sort bad]
  have he (P : bad) :
      (∑ ij ∈ allowed P.val,(eulerVariable ψ₁ P.val s₁)^ij.1*(eulerVariable ψ₂ P.val s₂)^ij.2) =
      ∑ ij : allowed P.val,(eulerVariable ψ₁ P.val s₁)^ij.val.1*(eulerVariable ψ₂ P.val s₂)^ij.val.2 :=
    (Finset.sum_coe_sort _ _).symm
  simp_rw [he]
  exact Fintype.prod_sum _

abbrev FullIndex (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) :=
  BadIndex bad allowed × GoodIndex bad

def fullSeriesTerm (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (s₁ s₂ : ℂ) (k : FullIndex bad allowed) : ℂ :=
  badSeriesTerm ψ₁ ψ₂ bad allowed s₁ s₂ k.1*goodSeriesTerm ψ₁ ψ₂ bad s₁ s₂ k.2

/-- Absolute convergence with the literal exceptional masks included. -/
theorem fullSeries_summable_norm (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (s₁ s₂ : ℂ)
    (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    Summable (fun k : FullIndex bad allowed => ‖fullSeriesTerm ψ₁ ψ₂ bad allowed s₁ s₂ k‖) := by
  have hb : Summable (fun k : BadIndex bad allowed => ‖badSeriesTerm ψ₁ ψ₂ bad allowed s₁ s₂ k‖) :=
    (hasSum_fintype _).summable
  have hg := goodSeries_summable_norm ψ₁ ψ₂ bad s₁ s₂ hs₁ hs₂
  have h := hb.mul_norm hg
  simpa only [fullSeriesTerm,norm_mul,norm_norm] using h

/-- Exact complete numerator series H10, with every finite exceptional local
polynomial and every signed good-prime monomial retained. -/
theorem fullSeries_expansion (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (s₁ s₂ : ℂ)
    (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    exceptionalProduct ψ₁ ψ₂ bad allowed s₁ s₂ *
      (∏' P : GoodPrimes bad,
        cubeFreeNumerator (eulerVariable ψ₁ P.val s₁) (eulerVariable ψ₂ P.val s₂)) =
    ∑' k : FullIndex bad allowed,fullSeriesTerm ψ₁ ψ₂ bad allowed s₁ s₂ k := by
  rw [badSeries_expansion,goodSeries_expansion ψ₁ ψ₂ bad s₁ s₂ hs₁ hs₂]
  have hb : Summable (badSeriesTerm ψ₁ ψ₂ bad allowed s₁ s₂) := (hasSum_fintype _).summable
  have hg := (goodSeries_summable_norm ψ₁ ψ₂ bad s₁ s₂ hs₁ hs₂).of_norm
  simpa only [tsum_fintype,fullSeriesTerm] using hb.tsum_mul_tsum hg
    (fullSeries_summable_norm ψ₁ ψ₂ bad allowed s₁ s₂ hs₁ hs₂).of_norm

/-- The actual extracted ideals from the good numerator monomials. -/
def goodIdeal₁ (bad : Finset PrimeIdeal) (k : GoodIndex bad) : Ideal O :=
  ∏ P : k.1,P.val.val.val^(h3Exponent (k.2 P)).1

def goodIdeal₂ (bad : Finset PrimeIdeal) (k : GoodIndex bad) : Ideal O :=
  ∏ P : k.1,P.val.val.val^(h3Exponent (k.2 P)).2

def badIdeal₁ (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (k : BadIndex bad allowed) : Ideal O := ∏ P : bad,P.val.val^(k P).val.1

def badIdeal₂ (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (k : BadIndex bad allowed) : Ideal O := ∏ P : bad,P.val.val^(k P).val.2

def fullIdeal₁ (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (k : FullIndex bad allowed) : Ideal O := badIdeal₁ bad allowed k.1*goodIdeal₁ bad k.2

def fullIdeal₂ (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (k : FullIndex bad allowed) : Ideal O := badIdeal₂ bad allowed k.1*goodIdeal₂ bad k.2

lemma goodIdeal₁_ne_zero (bad : Finset PrimeIdeal) (k : GoodIndex bad) : goodIdeal₁ bad k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => pow_ne_zero _ P.val.val.property.ne_zero)

lemma goodIdeal₂_ne_zero (bad : Finset PrimeIdeal) (k : GoodIndex bad) : goodIdeal₂ bad k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => pow_ne_zero _ P.val.val.property.ne_zero)

lemma badIdeal₁_ne_zero (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (k : BadIndex bad allowed) : badIdeal₁ bad allowed k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => pow_ne_zero _ P.val.property.ne_zero)

lemma badIdeal₂_ne_zero (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (k : BadIndex bad allowed) : badIdeal₂ bad allowed k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => pow_ne_zero _ P.val.property.ne_zero)

lemma fullIdeal₁_ne_zero (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (k : FullIndex bad allowed) : fullIdeal₁ bad allowed k ≠ 0 :=
  mul_ne_zero (badIdeal₁_ne_zero bad allowed k.1) (goodIdeal₁_ne_zero bad k.2)

lemma fullIdeal₂_ne_zero (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (k : FullIndex bad allowed) : fullIdeal₂ bad allowed k ≠ 0 :=
  mul_ne_zero (badIdeal₂_ne_zero bad allowed k.1) (goodIdeal₂_ne_zero bad k.2)

end
end QRH.Cycle092.SignedCenter
