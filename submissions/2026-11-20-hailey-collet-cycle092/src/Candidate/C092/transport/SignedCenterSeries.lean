/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.SignedCenterMask

/-! Explicit seven-monomial Euler convolution coefficients. The indexing retains
which prime supplied each monomial; absolute convergence is proved before any
regrouping by the resulting pair of ideals. -/
set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily

def h3Exponent (j : Fin 7) : ℕ×ℕ := ![(3,0),(2,1),(1,2),(0,3),(3,1),(2,2),(1,3)] j

def h3Sign (j : Fin 7) : ℂ := if j.val < 4 then -1 else 1

def h3Term (x y : ℂ) (j : Fin 7) : ℂ :=
  h3Sign j*x^(h3Exponent j).1*y^(h3Exponent j).2

lemma h3Term_sum (x y : ℂ) : ∑ j : Fin 7,h3Term x y j=cubeFreeNumerator x y-1 := by
  norm_num [h3Term,h3Exponent,h3Sign,Fin.sum_univ_succ,cubeFreeNumerator]
  ring

lemma h3Exponent_degree (j : Fin 7) : 3 ≤ (h3Exponent j).1+(h3Exponent j).2 := by
  fin_cases j <;> norm_num [h3Exponent]

lemma h3Sign_norm (j : Fin 7) : ‖h3Sign j‖=1 := by
  unfold h3Sign
  split_ifs <;> simp

lemma h3Term_norm_le (x y : ℂ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (j : Fin 7) : ‖h3Term x y j‖ ≤ r^3 := by
  rw [h3Term,norm_mul,norm_mul,h3Sign_norm,one_mul,norm_pow,norm_pow]
  calc
    _ ≤ r^(h3Exponent j).1*r^(h3Exponent j).2 := mul_le_mul
      (pow_le_pow_left₀ (norm_nonneg _) hx _) (pow_le_pow_left₀ (norm_nonneg _) hy _)
      (by positivity) (by positivity)
    _ = r^((h3Exponent j).1+(h3Exponent j).2) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_of_le_one hr hr1 (h3Exponent_degree j)

def primeTerm (ψ₁ ψ₂ : Character) (s₁ s₂ : ℂ) (P : PrimeIdeal) (j : Fin 7) : ℂ :=
  h3Term (eulerVariable ψ₁ P s₁) (eulerVariable ψ₂ P s₂) j

lemma primeTerm_sum (ψ₁ ψ₂ : Character) (s₁ s₂ : ℂ) (P : PrimeIdeal) :
    ∑ j : Fin 7,primeTerm ψ₁ ψ₂ s₁ s₂ P j=goodCorrection ψ₁ ψ₂ s₁ s₂ P :=
  h3Term_sum _ _

lemma primeTerm_norm_le (ψ₁ ψ₂ : Character) (s₁ s₂ : ℂ)
    (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re)
    (P : PrimeIdeal) (j : Fin 7) :
    ‖primeTerm ψ₁ ψ₂ s₁ s₂ P j‖ ≤ (Ideal.absNorm P.val : ℝ)^(-(6/5 : ℝ)) := by
  have h := h3Term_norm_le (eulerVariable ψ₁ P s₁) (eulerVariable ψ₂ P s₂)
    ((Ideal.absNorm P.val : ℝ)^(-(2/5 : ℝ)))
    (Real.rpow_nonneg (prime_norm_pos P).le _)
    (Real.rpow_le_one_of_one_le_of_nonpos (prime_norm_one_le P) (by norm_num))
    (eulerVariable_norm_bound ψ₁ P s₁ hs₁) (eulerVariable_norm_bound ψ₂ P s₂ hs₂) j
  change ‖h3Term (eulerVariable ψ₁ P s₁) (eulerVariable ψ₂ P s₂) j‖ ≤ _
  convert h using 1
  rw [←Real.rpow_natCast,←Real.rpow_mul (prime_norm_pos P).le]
  norm_num

lemma primeTerm_mass_summable (ψ₁ ψ₂ : Character) (s₁ s₂ : ℂ)
    (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    Summable (fun P : PrimeIdeal => ∑ j : Fin 7,‖primeTerm ψ₁ ψ₂ s₁ s₂ P j‖) := by
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
  apply (hm.mul_left 7).of_nonneg_of_le (fun P => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro P
  calc
    _ ≤ ∑ _j : Fin 7,(Ideal.absNorm P.val : ℝ)^(-(6/5 : ℝ)) :=
      Finset.sum_le_sum (fun j _ => primeTerm_norm_le ψ₁ ψ₂ s₁ s₂ hs₁ hs₂ P j)
    _ = _ := by simp

/-- Each prime occurs at most once; the chosen monomial records the two
valuation exponents and its genuine signed character coefficient. -/
abbrev GoodIndex (bad : Finset PrimeIdeal) :=
  Σ S : Finset (GoodPrimes bad),S → Fin 7

def goodSeriesTerm (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (s₁ s₂ : ℂ) (k : GoodIndex bad) : ℂ :=
  ∏ P : k.1,primeTerm ψ₁ ψ₂ s₁ s₂ P.val.val (k.2 P)

/-- Absolute convergence of the explicit seven-choice convolution series, not
merely the polynomial correction after local cancellation. -/
theorem goodSeries_summable_norm (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (s₁ s₂ : ℂ) (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    Summable (fun k : GoodIndex bad => ‖goodSeriesTerm ψ₁ ψ₂ bad s₁ s₂ k‖) := by
  have hm : Summable (fun P : GoodPrimes bad => ∑ j : Fin 7,‖primeTerm ψ₁ ψ₂ s₁ s₂ P.val j‖) :=
    (primeTerm_mass_summable ψ₁ ψ₂ s₁ s₂ hs₁ hs₂).subtype (fun P => P ∉ bad)
  have hp := summable_finsetProd_of_summable_nonneg
    (fun P : GoodPrimes bad => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hm
  apply (summable_sigma_of_nonneg (fun k : GoodIndex bad => norm_nonneg
    (goodSeriesTerm ψ₁ ψ₂ bad s₁ s₂ k))).mpr
  refine ⟨fun S => (hasSum_fintype _).summable,?_⟩
  apply hp.congr
  intro S
  rw [tsum_fintype]
  change (∏ P ∈ S,∑ j : Fin 7,‖primeTerm ψ₁ ψ₂ s₁ s₂ P.val j‖)=_
  rw [←Finset.prod_coe_sort S, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _hf
  simp only [goodSeriesTerm,norm_prod]

theorem goodSeries_expansion (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (s₁ s₂ : ℂ) (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    (∏' P : GoodPrimes bad,
      cubeFreeNumerator (eulerVariable ψ₁ P.val s₁) (eulerVariable ψ₂ P.val s₂)) =
    ∑' k : GoodIndex bad,goodSeriesTerm ψ₁ ψ₂ bad s₁ s₂ k := by
  rw [good_product_expansion ψ₁ ψ₂ bad s₁ s₂ hs₁ hs₂,
    (goodSeries_summable_norm ψ₁ ψ₂ bad s₁ s₂ hs₁ hs₂).of_norm.tsum_sigma]
  apply tsum_congr
  intro S
  rw [tsum_fintype]
  change (∏ P ∈ S,goodCorrection ψ₁ ψ₂ s₁ s₂ P.val)=_
  simp_rw [←primeTerm_sum]
  rw [←Finset.prod_coe_sort S,Fintype.prod_sum]
  rfl

end
end QRH.Cycle092.SignedCenter
