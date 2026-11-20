/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Weighted physical Hölder integration, preserving selected prime exponent two
and full prime factors separately. The finite kernels retain their original
OpenAI/Collet/Levy/Gao provenance; only elementary integration is added here. -/
import Candidate.C092.transport.DirectWeightedKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace QRH.Cycle092.DirectEnergy.Packet

/-- First weighted integral from the genuine fourth moment, with exact finite
cardinality. No optimized count, endpoint bound or already-integrated physical
estimate is a premise. The kernel may retain all independent height variables. -/
theorem weighted_first_integral {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (rows : Finset ι) (S Q P : Ω → ι → ℂ) (K : Ω → ℂ)
    (L A E : ℝ) (hL : 0 < L) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hK : Integrable K μ)
    (hselected : ∀ t, ∀ i ∈ rows, L ≤ ‖Q t i‖)
    (hfull : ∀ t, ∀ i ∈ rows, ‖P t i‖ ≤ A)
    (hmoment : ∀ t, (∑ i ∈ rows, ‖S t i‖^4*‖Q t i‖^2) ≤ E) :
    L^2*‖∫ t, K t*(∑ i ∈ rows, S t i*P t i) ∂μ‖^4 ≤
      A^4*(rows.card : ℝ)^3*E*(∫ t, ‖K t‖ ∂μ)^4 := by
  let C : ℝ := (A^4*(rows.card : ℝ)^3*E)/L^2
  let B : ℝ := Real.sqrt (Real.sqrt C)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBpow : B^4=C := by
    dsimp [B]
    calc
      (Real.sqrt (Real.sqrt C))^4 = ((Real.sqrt (Real.sqrt C))^2)^2 := by ring
      _ = (Real.sqrt C)^2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg C)]
      _ = C := Real.sq_sqrt hC
  have hpoint (t : Ω) : ‖∑ i ∈ rows, S t i*P t i‖ ≤ B := by
    have hh := weighted_row_holder_with_full rows (S t) (Q t) (P t) L A hL.le hA
      (hselected t) (hfull t)
    have hmoment' := mul_le_mul_of_nonneg_left (hmoment t)
      (by positivity : 0 ≤ A^4*(rows.card : ℝ)^3)
    have hf : (∑ i ∈ rows, ‖S t i*P t i‖)^4 ≤ C := by
      dsimp [C]
      apply (le_div_iff₀ (sq_pos_of_pos hL)).2
      nlinarith only [hh,hmoment']
    rw [← hBpow] at hf
    have hs : (∑ i ∈ rows, ‖S t i*P t i‖) ≤ B :=
      (pow_le_pow_iff_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
        hB (by norm_num : (4 : ℕ) ≠ 0)).mp hf
    exact (norm_sum_le _ _).trans hs
  have hI : ‖∫ t, K t*(∑ i ∈ rows, S t i*P t i) ∂μ‖ ≤
      (∫ t, ‖K t‖ ∂μ)*B := by
    have hb := norm_integral_le_of_norm_le (f := fun t => K t*(∑ i ∈ rows, S t i*P t i)) (hK.norm.mul_const B)
      (Filter.Eventually.of_forall fun t => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hpoint t) (norm_nonneg _))
    simpa only [integral_mul_const] using hb
  have hLB : L^2*B^4=A^4*(rows.card : ℝ)^3*E := by
    rw [hBpow]
    dsimp [C]
    field_simp [ne_of_gt (sq_pos_of_pos hL)]
  calc
    _ ≤ L^2*((∫ t, ‖K t‖ ∂μ)*B)^4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hI 4) (sq_nonneg _)
    _ = (∫ t, ‖K t‖ ∂μ)^4*(L^2*B^4) := by ring
    _ = _ := by rw [hLB]; ring
end QRH.Cycle092.DirectEnergy.Packet
#print axioms QRH.Cycle092.DirectEnergy.Packet.weighted_first_integral
