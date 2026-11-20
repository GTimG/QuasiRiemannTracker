/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.SignedCenterClearing

/-! Global signed 3/5 estimate with finite exceptional Euler clearing for the explicit genuine Euler-coefficient
correctedConvolution. It uses the checked weighted coefficient mass and the actual
fixed-row lattice theorem, with independent normalized profile heights.
The remaining source-binding boundary is stated in SignedCenterConvolution.
-/
set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O


def correctedMass (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) : ℝ :=
  ∑' k : CorrectedIndex bad allowed,‖correctedCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed k‖*
    ((Ideal.absNorm (correctedIdeal₁ bad allowed k) : ℝ)*
      (Ideal.absNorm (correctedIdeal₂ bad allowed k) : ℝ))^(-(2/5 : ℝ))

def correctedConvolutionTerm (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (x y : ℝ)
    (k : CorrectedIndex bad allowed) : ℂ :=
  correctedCoefficient R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed k*
    pairSource R₁ R₂ P₁ P₂ (x/(Ideal.absNorm (correctedIdeal₁ bad allowed k) : ℝ))
      (y/(Ideal.absNorm (correctedIdeal₂ bad allowed k) : ℝ))

def correctedConvolutionSource (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (x y : ℝ) : ℂ :=
  ∑' k : CorrectedIndex bad allowed,correctedConvolutionTerm R₁ R₂ P₁ P₂ bad allowed x y k

lemma correctedConvolutionTerm_absolute (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (k : CorrectedIndex bad allowed) :
    ‖correctedConvolutionTerm R₁ R₂ P₁ P₂ bad allowed x y k‖ ≤
      ((pairC P₁ P₂)^2*(x*y))*(‖correctedCoefficient R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed k‖*
        ((Ideal.absNorm (correctedIdeal₁ bad allowed k) : ℝ)*
          (Ideal.absNorm (correctedIdeal₂ bad allowed k) : ℝ))^(-(2/5 : ℝ))) := by
  let d₁ : ℝ := Ideal.absNorm (correctedIdeal₁ bad allowed k)
  let d₂ : ℝ := Ideal.absNorm (correctedIdeal₂ bad allowed k)
  have hd₁ : 1 ≤ d₁ := nonzero_ideal_norm_one_le _ (correctedIdeal₁_ne_zero bad allowed k)
  have hd₂ : 1 ≤ d₂ := nonzero_ideal_norm_one_le _ (correctedIdeal₂_ne_zero bad allowed k)
  have hd₁p : 0 < d₁ := zero_lt_one.trans_le hd₁
  have hd₂p : 0 < d₂ := zero_lt_one.trans_le hd₂
  have hi : 1/(d₁*d₂) ≤ (d₁*d₂)^(-(2/5 : ℝ)) := by
    simpa only [Real.rpow_neg_one,one_div] using Real.rpow_le_rpow_of_exponent_le
      (one_le_mul_of_one_le_of_one_le hd₁ hd₂) (by norm_num : (-1 : ℝ) ≤ -(2/5 : ℝ))
  have ha := pairSource_absolute R₁ R₂ P₁ P₂ _ _ (div_pos hx hd₁p) (div_pos hy hd₂p)
  rw [div_mul_div_comm] at ha
  rw [correctedConvolutionTerm,norm_mul]
  have hfirst := mul_le_mul_of_nonneg_left ha (norm_nonneg (correctedCoefficient R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed k))
  have hlast := mul_le_mul_of_nonneg_left hi
    (mul_nonneg (mul_nonneg (sq_nonneg (pairC P₁ P₂)) (mul_nonneg hx.le hy.le))
      (norm_nonneg (correctedCoefficient R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed k)))
  exact hfirst.trans ((by convert hlast using 1 <;> ring))

/-- Both correctedConvolution arms converge absolutely before signed cancellation. -/
theorem correctedConvolutionSource_summable_norm (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    Summable (fun k : CorrectedIndex bad allowed => ‖correctedConvolutionTerm R₁ R₂ P₁ P₂ bad allowed x y k‖) := by
  exact ((correctedCoefficient_weighted_summable R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed).mul_left
    ((pairC P₁ P₂)^2*(x*y))).of_nonneg_of_le (fun _ => norm_nonneg _)
      (correctedConvolutionTerm_absolute R₁ R₂ P₁ P₂ bad allowed x y hx hy)

/-- A global signed H8-strength bound for the explicit coefficient correctedConvolution.
Every coefficient and extracted ideal is genuine, no stored analytic margin or
assumed summability is used, and the profile heights remain independent. -/
theorem correctedConvolutionSource_signed_saving (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 0 < L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T) :
    ‖(Real.sqrt T : ℂ)⁻¹*(correctedConvolutionSource R₁ R₂ P₁ P₂ bad allowed X₁ X₂-
      correctedConvolutionSource R₁ R₂ P₁ P₂ bad allowed Y₁ Y₂)‖ ≤
    pairK R₁ R₂ P₁ P₂*correctedMass R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed*
      Real.sqrt T*L^(-(3/5 : ℝ)) := by
  have hT : 0 < T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hA := correctedConvolutionSource_summable_norm R₁ R₂ P₁ P₂ bad allowed X₁ X₂ (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hB := correctedConvolutionSource_summable_norm R₁ R₂ P₁ P₂ bad allowed Y₁ Y₂ (hL.trans_le hY₁) (hL.trans_le hY₂)
  have hm := correctedCoefficient_weighted_summable R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed
  have hterm (k : CorrectedIndex bad allowed) :
      ‖correctedConvolutionTerm R₁ R₂ P₁ P₂ bad allowed X₁ X₂ k-
        correctedConvolutionTerm R₁ R₂ P₁ P₂ bad allowed Y₁ Y₂ k‖ ≤
      (pairK R₁ R₂ P₁ P₂*T*L^(-(3/5 : ℝ)))*
        (‖correctedCoefficient R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed k‖*
          ((Ideal.absNorm (correctedIdeal₁ bad allowed k) : ℝ)*
            (Ideal.absNorm (correctedIdeal₂ bad allowed k) : ℝ))^(-(2/5 : ℝ))) := by
    have h := pairSource_scaled_saving R₁ R₂ P₁ P₂
      (Ideal.absNorm (correctedIdeal₁ bad allowed k)) (Ideal.absNorm (correctedIdeal₂ bad allowed k))
      X₁ X₂ Y₁ Y₂ T L
      (nonzero_ideal_norm_one_le _ (correctedIdeal₁_ne_zero bad allowed k))
      (nonzero_ideal_norm_one_le _ (correctedIdeal₂_ne_zero bad allowed k))
      hL hX₁ hX₂ hY₁ hY₂ hpX hpY
    rw [correctedConvolutionTerm,correctedConvolutionTerm,←mul_sub,norm_mul]
    exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (by ring)
  have hraw : ‖correctedConvolutionSource R₁ R₂ P₁ P₂ bad allowed X₁ X₂-
      correctedConvolutionSource R₁ R₂ P₁ P₂ bad allowed Y₁ Y₂‖ ≤
      (pairK R₁ R₂ P₁ P₂*correctedMass R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed*L^(-(3/5 : ℝ)))*T := by
    rw [correctedConvolutionSource,correctedConvolutionSource,←hA.of_norm.tsum_sub hB.of_norm]
    have hnorm := (hA.of_norm.sub hB.of_norm).norm
    have hsum := hnorm.tsum_le_tsum hterm (hm.mul_left (pairK R₁ R₂ P₁ P₂*T*L^(-(3/5 : ℝ))))
    rw [tsum_mul_left] at hsum
    exact (norm_tsum_le_tsum_norm hnorm).trans (hsum.trans_eq (by unfold correctedMass; ring))
  exact (normalized_of_raw _ T _ hT hraw).trans_eq (by ring)

end
end QRH.Cycle092.SignedCenter
