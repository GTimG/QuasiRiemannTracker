/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Positive restriction from the authentic all-row first-Poisson energy to
any retained finite original row set. No nonprincipal gate is weakened. -/
import Candidate.C092.transport.ReferenceShortP3Uncentered
import Candidate.C092.transport.StrongPairFinite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ReferenceShortP3
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentRowNorm
open CenteredMomentPlainEnergy
local notation "O" => HeckeFamily.O

theorem finite_rows_le_source
    (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (hml : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (rows : Finset O)
    (hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z∈rows, 1 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) :
    (∑ z∈rows, ‖∑ I∈S,c I*rowWeight η m A z t I‖^2) ≤
      ‖finiteHeckeEnergy η m A t S c Φ K‖ := by
  let a := sourceGenerator S
  let β := fun I : supportedColumns S => c I*rowWeight η m A 1 t I
  have hs := Complex.hasSum_re
    (rowEnergy_summable Finset.univ a (sourceGenerator_supported S) β Φ K hK).hasSum
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  have hbound : (∑ z∈rows, ‖rowPolynomial Finset.univ a β z‖^2) ≤
      (rowEnergy Finset.univ a β Φ K).re := by
    apply le_trans (Finset.sum_le_sum (fun z hz =>
      le_mul_of_one_le_right (sq_nonneg _) (hmajor z hz)))
    exact sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hΦ z)) hs
  have heq := finiteHeckeEnergy_eq η m A t hml hm2 S c Φ K
  apply le_trans (le_of_eq ?_) (hbound.trans ?_)
  · apply Finset.sum_congr rfl
    intro z hz
    rw [finite_hecke_sum_eq_rowPolynomial η m A z t hml hm2 S c]
  · rw [heq]
    exact Complex.re_le_norm _

/-- Literal product normalization of the short fourth. The same positive
volume appears in the square-root coefficient and in the Poisson bound. -/
theorem finite_normalized_rows_le_source
    (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (K V : ℝ) (hK : 0 < K) (hV : 0 < V)
    (hml : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (rows : Finset O)
    (hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z∈rows, 1 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) :
    (∑ z∈rows, ‖((Real.sqrt V : ℝ) : ℂ)⁻¹ *
      (∑ I∈S,c I*rowWeight η m A z t I)‖^2) ≤
      ‖finiteHeckeEnergy η m A t S c Φ K‖/V := by
  have hb := finite_rows_le_source η m A t S c Φ K hK hml hm2 rows hΦ hmajor
  have hn : ‖((Real.sqrt V : ℝ) : ℂ)⁻¹‖^2 = V⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,Real.sq_sqrt hV.le]
  simp only [norm_mul,mul_pow,hn,←Finset.mul_sum]
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hV.le)

#print axioms finite_rows_le_source
#print axioms finite_normalized_rows_le_source
end
end QRH.Cycle092.ReferenceShortP3
