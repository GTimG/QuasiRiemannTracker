/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.SignedCenterCorrected

/-! Uniform coefficient control and the complete max(1,L)^(-3/5) estimate for
the corrected actual-row Euler convolution, with all finite mask clearing.
-/
set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily

lemma coefficientMass_eq_norm (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) :
    coefficientMass ψ₁ ψ₂ bad allowed=
      ∑' k : FullIndex bad allowed,‖fullSeriesTerm ψ₁ ψ₂ bad allowed (2/5 : ℂ) (2/5 : ℂ) k‖ := by
  unfold coefficientMass
  apply tsum_congr
  intro k
  rw [fullSeriesTerm_coefficient,norm_mul,norm_mul,
    normWeight_critical _ (fullIdeal₁_ne_zero bad allowed k),
    normWeight_critical _ (fullIdeal₂_ne_zero bad allowed k),
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

lemma correctedMass_eq_product (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) :
    correctedMass χ₁ χ₂ ψ₁ ψ₂ bad allowed=
      (∑ k : DeletionIndex bad,‖deletionSeriesTerm χ₁ χ₂ bad (2/5 : ℂ) (2/5 : ℂ) k‖)*
      coefficientMass ψ₁ ψ₂ bad allowed := by
  have he (k : CorrectedIndex bad allowed) :
      ‖correctedCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed k‖*
        ((Ideal.absNorm (correctedIdeal₁ bad allowed k) : ℝ)*
          (Ideal.absNorm (correctedIdeal₂ bad allowed k) : ℝ))^(-(2/5 : ℝ)) =
      ‖correctedSeriesTerm χ₁ χ₂ ψ₁ ψ₂ bad allowed (2/5 : ℂ) (2/5 : ℂ) k‖ := by
    rw [correctedSeriesTerm_coefficient,norm_mul,norm_mul,
      normWeight_critical _ (correctedIdeal₁_ne_zero bad allowed k),
      normWeight_critical _ (correctedIdeal₂_ne_zero bad allowed k),
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  unfold correctedMass
  simp_rw [he]
  rw [(correctedSeries_summable_norm χ₁ χ₂ ψ₁ ψ₂ bad allowed (2/5 : ℂ) (2/5 : ℂ)
    (by norm_num) (by norm_num)).tsum_prod]
  simp only [correctedSeriesTerm,norm_mul,tsum_mul_left]
  rw [tsum_mul_right,tsum_fintype,coefficientMass_eq_norm]

theorem correctedMass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
      (allowed : PrimeIdeal → Finset (ℕ×ℕ)),
      (∀ P ∈ bad,allowed P ⊆ residualPairs true true) →
      correctedMass χ₁ χ₂ ψ₁ ψ₂ bad allowed ≤ C*(Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ)^ε := by
  obtain ⟨C₁,hC₁,h₁⟩ := six_pow_card_subpower (ε/2) (by linarith)
  obtain ⟨C₂,hC₂,h₂⟩ := coefficientMass_subpower (ε/2) (by linarith)
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro χ₁ χ₂ ψ₁ ψ₂ bad allowed hallowed
  have hm : 0 ≤ coefficientMass ψ₁ ψ₂ bad allowed := by
    rw [coefficientMass_eq_norm]
    exact tsum_nonneg (fun _ => norm_nonneg _)
  have hd := (deletionSeries_mass_le χ₁ χ₂ bad (2/5 : ℂ) (2/5 : ℂ) (by norm_num) (by norm_num)).trans
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (4 : ℝ) ≤ 6) bad.card)
  have hn : 0 < (Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ) := by
    exact zero_lt_one.trans_le (nonzero_ideal_norm_one_le _ (SmoothMobiusCorrection.primeProduct_ne_zero bad))
  rw [correctedMass_eq_product]
  calc
    _ ≤ (6 : ℝ)^bad.card*coefficientMass ψ₁ ψ₂ bad allowed := mul_le_mul_of_nonneg_right hd hm
    _ ≤ (C₁*(Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ)^(ε/2))*
        (C₂*(Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ)^(ε/2)) :=
      mul_le_mul (h₁ bad) (h₂ ψ₁ ψ₂ bad allowed hallowed) hm
        (mul_nonneg hC₁.le (Real.rpow_nonneg hn.le _))
    _ = (C₁*C₂)*(Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ)^ε := by
      rw [show ε=ε/2+ε/2 by ring,Real.rpow_add hn]
      ring

/-- Literal numerator identity with original ordinary Euler factors retained. -/
theorem correctedSeries_expansion (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (s₁ s₂ : ℂ)
    (hs₁ : (2/5 : ℝ) ≤ s₁.re) (hs₂ : (2/5 : ℝ) ≤ s₂.re) :
    (∏ P ∈ bad,(1-eulerVariable χ₁ P s₁)*(1-eulerVariable χ₂ P s₂))*
      (exceptionalProduct ψ₁ ψ₂ bad allowed s₁ s₂*
        (∏' P : GoodPrimes bad,cubeFreeNumerator (eulerVariable ψ₁ P.val s₁) (eulerVariable ψ₂ P.val s₂))) =
    ∑' k : CorrectedIndex bad allowed,correctedSeriesTerm χ₁ χ₂ ψ₁ ψ₂ bad allowed s₁ s₂ k := by
  rw [deletionSeries_expansion,fullSeries_expansion ψ₁ ψ₂ bad allowed s₁ s₂ hs₁ hs₂]
  have hd : Summable (deletionSeriesTerm χ₁ χ₂ bad s₁ s₂) := (hasSum_fintype _).summable
  have hf := (fullSeries_summable_norm ψ₁ ψ₂ bad allowed s₁ s₂ hs₁ hs₂).of_norm
  simpa only [tsum_fintype,correctedSeriesTerm] using hd.tsum_mul_tsum hf
    (correctedSeries_summable_norm χ₁ χ₂ ψ₁ ψ₂ bad allowed s₁ s₂ hs₁ hs₂).of_norm

lemma correctedConvolutionSource_absolute (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    ‖correctedConvolutionSource R₁ R₂ P₁ P₂ bad allowed x y‖ ≤
      (pairC P₁ P₂)^2*(x*y)*correctedMass R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed := by
  have hnorm := correctedConvolutionSource_summable_norm R₁ R₂ P₁ P₂ bad allowed x y hx hy
  have hm := correctedCoefficient_weighted_summable R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed
  have hsum := hnorm.tsum_le_tsum (correctedConvolutionTerm_absolute R₁ R₂ P₁ P₂ bad allowed x y hx hy)
    (hm.mul_left ((pairC P₁ P₂)^2*(x*y)))
  rw [tsum_mul_left] at hsum
  exact (norm_tsum_le_tsum_norm hnorm).trans hsum

/-- The max(1,L) form includes the small-scale range by absolute counting. -/
theorem correctedConvolutionSource_signed_max (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 0 < L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T) :
    ‖(Real.sqrt T : ℂ)⁻¹*(correctedConvolutionSource R₁ R₂ P₁ P₂ bad allowed X₁ X₂-
      correctedConvolutionSource R₁ R₂ P₁ P₂ bad allowed Y₁ Y₂)‖ ≤
    pairK R₁ R₂ P₁ P₂*correctedMass R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed*
      Real.sqrt T*(max 1 L)^(-(3/5 : ℝ)) := by
  by_cases hbig : 1 ≤ L
  · rw [max_eq_right hbig]
    exact correctedConvolutionSource_signed_saving R₁ R₂ P₁ P₂ bad allowed
      X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  · rw [max_eq_left (le_of_not_ge hbig),Real.one_rpow,mul_one]
    have hT : 0 < T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
    have ha := correctedConvolutionSource_absolute R₁ R₂ P₁ P₂ bad allowed X₁ X₂ (hL.trans_le hX₁) (hL.trans_le hX₂)
    have hb := correctedConvolutionSource_absolute R₁ R₂ P₁ P₂ bad allowed Y₁ Y₂ (hL.trans_le hY₁) (hL.trans_le hY₂)
    rw [hpX] at ha
    rw [hpY] at hb
    have hmass : 0 ≤ correctedMass R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed :=
      tsum_nonneg (fun _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))
    have hK : 2*(pairC P₁ P₂)^2 ≤ pairK R₁ R₂ P₁ P₂ := by
      dsimp only [pairK]
      have hh := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (pairE_nonneg R₁ R₂ P₁ P₂)) (pairC_nonneg P₁ P₂)
      linarith
    apply normalized_of_raw _ T _ hT
    exact (norm_sub_le _ _).trans ((add_le_add ha hb).trans
      ((by convert mul_le_mul_of_nonneg_right hK (mul_nonneg hT.le hmass) using 1 <;> ring)))

/-- H8-strength saving for the corrected actual-row convolution, with a genuine
subpower exceptional cost and no character-coincidence or principal exclusions. -/
theorem correctedConvolutionSource_signed_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
      (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)),
      (∀ P ∈ bad,allowed P ⊆ residualPairs true true) →
      ∀ X₁ X₂ Y₁ Y₂ T L : ℝ,0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T : ℂ)⁻¹*(correctedConvolutionSource R₁ R₂ P₁ P₂ bad allowed X₁ X₂-
        correctedConvolutionSource R₁ R₂ P₁ P₂ bad allowed Y₁ Y₂)‖ ≤
      pairK R₁ R₂ P₁ P₂*C*(Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ)^ε*
        Real.sqrt T*(max 1 L)^(-(3/5 : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := correctedMass_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro R₁ R₂ P₁ P₂ bad allowed hallowed X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have h := correctedConvolutionSource_signed_max R₁ R₂ P₁ P₂ bad allowed
    X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  exact h.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (hbound R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed hallowed) (pairK_nonneg R₁ R₂ P₁ P₂))
      (Real.sqrt_nonneg T)) (Real.rpow_nonneg (zero_le_one.trans (le_max_left 1 L)) (-(3/5 : ℝ)))).trans_eq (by ring))

end
end QRH.Cycle092.SignedCenter
