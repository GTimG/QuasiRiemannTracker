/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.SignedCenterEuler
import Mathlib.Analysis.Normed.Ring.InfiniteProd

/-! Absolute convergence of the genuine H9 good-prime product, and its exact
finite-subset series expansion on the closed 2/5 strip. No reciprocal L-function
or nonprincipal-character assumption enters these statements. -/
set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
abbrev PrimeIdeal := SmoothMobiusCorrection.PrimeIdeal
local notation "O" => HeckeFamily.O

/-- Actual character-valued local ordinary Euler variable. -/
def eulerVariable (ψ : Character) (P : PrimeIdeal) (s : ℂ) : ℂ :=
  idealCoeff ψ P.val*(Ideal.absNorm P.val : ℂ)^(-s)

def goodCorrection (ψ₁ ψ₂ : Character) (s₁ s₂ : ℂ) (P : PrimeIdeal) : ℂ :=
  cubeFreeNumerator (eulerVariable ψ₁ P s₁) (eulerVariable ψ₂ P s₂)-1

lemma prime_norm_pos (P : PrimeIdeal) : 0 < (Ideal.absNorm P.val : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero (fun h => P.property.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)))

lemma prime_norm_one_le (P : PrimeIdeal) : 1 ≤ (Ideal.absNorm P.val : ℝ) := by
  have h := prime_norm_pos P
  have hn : 0 < Ideal.absNorm P.val := by exact_mod_cast h
  exact_mod_cast hn

lemma eulerVariable_norm_bound (ψ : Character) (P : PrimeIdeal) (s : ℂ)
    (hs : (2/5 : ℝ) ≤ s.re) :
    ‖eulerVariable ψ P s‖ ≤ (Ideal.absNorm P.val : ℝ)^(-(2/5 : ℝ)) := by
  unfold eulerVariable
  rw [norm_mul]
  have hw : ‖(Ideal.absNorm P.val : ℂ)^(-s)‖ =
      (Ideal.absNorm P.val : ℝ)^(-s.re) := by
    change ‖((Ideal.absNorm P.val : ℝ) : ℂ)^(-s)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P)]
    rfl
  rw [hw]
  exact (mul_le_of_le_one_left (Real.rpow_nonneg (prime_norm_pos P).le _)
    (idealCoeff_norm_le_one ψ P.val)).trans
    (Real.rpow_le_rpow_of_exponent_le (prime_norm_one_le P) (neg_le_neg hs))

lemma goodCorrection_norm_bound (ψ₁ ψ₂ : Character) (s₁ s₂ : ℂ)
    (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) (P : PrimeIdeal) :
    ‖goodCorrection ψ₁ ψ₂ s₁ s₂ P‖ ≤
      7*(Ideal.absNorm P.val : ℝ)^(-(6/5 : ℝ)) := by
  have h := cubeFreeNumerator_error (eulerVariable ψ₁ P s₁) (eulerVariable ψ₂ P s₂)
    ((Ideal.absNorm P.val : ℝ)^(-(2/5 : ℝ)))
    (Real.rpow_nonneg (prime_norm_pos P).le _)
    (Real.rpow_le_one_of_one_le_of_nonpos (prime_norm_one_le P) (by norm_num))
    (eulerVariable_norm_bound ψ₁ P s₁ hs₁) (eulerVariable_norm_bound ψ₂ P s₂ hs₂)
  change ‖cubeFreeNumerator (eulerVariable ψ₁ P s₁) (eulerVariable ψ₂ P s₂)-1‖ ≤ _
  convert h using 1
  rw [←Real.rpow_natCast,←Real.rpow_mul (prime_norm_pos P).le]
  norm_num

/-- Absolute norm convergence on the closed strip, via the checked Eisenstein
Dedekind series at 6/5. This includes equal and principal character pairs. -/
theorem goodCorrection_summable_norm (ψ₁ ψ₂ : Character) (s₁ s₂ : ℂ)
    (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    Summable (fun P : PrimeIdeal => ‖goodCorrection ψ₁ ψ₂ s₁ s₂ P‖) := by
  have hs := (CubicEisenstein.fullIdealWeight_summable_norm (6/5 : ℂ)
    (by norm_num)).comp_injective
      (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal => P.val))
  have hm : Summable (fun P : PrimeIdeal => (Ideal.absNorm P.val : ℝ)^(-(6/5 : ℝ))) := by
    apply hs.congr
    intro P
    rw [Function.comp_apply,CubicEisenstein.fullIdealWeight,ite_eq_right P.property.ne_zero]
    change ‖((Ideal.absNorm P.val : ℝ) : ℂ)^(-(6/5 : ℂ))‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P)]
    norm_num
  exact (hm.mul_left 7).of_nonneg_of_le (fun _ => norm_nonneg _)
    (goodCorrection_norm_bound ψ₁ ψ₂ s₁ s₂ hs₁ hs₂)

/-- Good primes outside the actual finite exceptional set. -/
abbrev GoodPrimes (bad : Finset PrimeIdeal) := {P : PrimeIdeal // P ∉ bad}

theorem good_product_multipliable (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (s₁ s₂ : ℂ) (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    Multipliable (fun P : GoodPrimes bad =>
      cubeFreeNumerator (eulerVariable ψ₁ P.val s₁) (eulerVariable ψ₂ P.val s₂)) := by
  have hs := (goodCorrection_summable_norm ψ₁ ψ₂ s₁ s₂ hs₁ hs₂).subtype
    (fun P => P ∉ bad)
  have hp := multipliable_one_add_of_summable hs
  simpa only [goodCorrection,add_sub_cancel] using hp

/-- Exact global series identity for the good Euler numerator product. Its
terms are products of the genuine coupled local corrections over finite sets. -/
theorem good_product_expansion (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (s₁ s₂ : ℂ) (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    (∏' P : GoodPrimes bad,
      cubeFreeNumerator (eulerVariable ψ₁ P.val s₁) (eulerVariable ψ₂ P.val s₂)) =
    ∑' S : Finset (GoodPrimes bad), ∏ P ∈ S,goodCorrection ψ₁ ψ₂ s₁ s₂ P.val := by
  have hs := (goodCorrection_summable_norm ψ₁ ψ₂ s₁ s₂ hs₁ hs₂).subtype
    (fun P => P ∉ bad)
  have he := tprod_one_add (summable_finsetProd_of_summable_norm hs)
  simpa only [goodCorrection,add_sub_cancel] using he

/-- The exact expansion above converges absolutely, rather than only as a
conditionally convergent product. -/
theorem good_expansion_summable_norm (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (s₁ s₂ : ℂ) (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    Summable (fun S : Finset (GoodPrimes bad) =>
      ‖∏ P ∈ S,goodCorrection ψ₁ ψ₂ s₁ s₂ P.val‖) := by
  have hs := (goodCorrection_summable_norm ψ₁ ψ₂ s₁ s₂ hs₁ hs₂).subtype
    (fun P => P ∉ bad)
  have h : Summable (fun S : Finset (GoodPrimes bad) =>
      ∏ P ∈ S, ‖goodCorrection ψ₁ ψ₂ s₁ s₂ P.val‖) :=
    summable_finsetProd_of_summable_nonneg (fun P : GoodPrimes bad =>
      norm_nonneg (goodCorrection ψ₁ ψ₂ s₁ s₂ P.val)) hs
  simpa only [norm_prod] using h

end
end QRH.Cycle092.SignedCenter
