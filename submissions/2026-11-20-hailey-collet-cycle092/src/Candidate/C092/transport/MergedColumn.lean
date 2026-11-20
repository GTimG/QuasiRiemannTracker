/- Copyright (c) 2026 Hailey Collet. Apache-2.0. Uses Joseph Bebel's
whole-word divisor bound and the original OAI ordinary-ideal row feature. -/
import Candidate.C092.transport.HighResponse
import Submissions.arvi_selected_leaf.JointDetector.SlotWordProducer
import Submissions.arvi_selected_leaf.JointDetector.ActualSlotData

namespace QRH.Cycle092.MergedColumn
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentAddedZero CenteredMomentSourceMass
open Qrh.JointDetector WholeWordAmplification SlotWordProducer
local notation "O" => ActualEisensteinCubic.O

/-- All factors share the original row feature. The coefficient can have arbitrary
joint deletions before regrouping: no factorization of a coprimality mask is needed.
The power of X is paid only once, even when there are many marked slots. -/
theorem masked_word_energy (rows : Finset O) {r : ℕ} (pools : Fin r → Finset (Ideal O))
    (c : Fin r → Ideal O → ℂ) (mask : (Fin r → Ideal O) → ℂ)
    (C cap : Fin r → ℝ) (K X ε : ℝ) (hK : 0 ≤ K) (hX : 1 ≤ X) (hε : 0 < ε)
    (hnz : ∀ i, ∀ I ∈ pools i, I ≠ 0) (hn : ∀ i, ∀ I ∈ pools i, (I.absNorm:ℝ) ≤ cap i)
    (hcaps : ∏ i, cap i ≤ X)
    (hc : ∀ i, (∑ I ∈ pools i, ‖c i I‖^2) ≤ C i)
    (hm : ∀ v ∈ wordTuples pools, ‖mask v‖ ≤ 1)
    (hsource : ∀ (S : Finset (Ideal O)) (a : S → ℂ), (∀ I ∈ S, (I.absNorm:ℝ) ≤ X) →
      ∑ z : rows, ‖FineDetectorWords.ordinaryPolynomial S a z.val‖^2 ≤ K * ∑ I, ‖a I‖^2) :
    (∑ z : rows, ‖∑ v ∈ wordTuples pools,
      (mask v * wordCoefficient c v) * idealRowHom z.val (tupleProduct v)‖^2) ≤
      K * ((wordDivisorConstant r ε hε * X^ε) * ∏ i, C i) := by
  let B := wordTuples pools
  let a := fun v => mask v * wordCoefficient c v
  have hN (I : Ideal O) (h : I ∈ tupleColumns B) := (word_source_norm pools cap hn I h).trans hcaps
  have hcols := hsource (tupleColumns B) (fun I => tupleCoefficient B a I.val) hN
  have hsum (z : O) : (∑ v ∈ B, a v * idealRowHom z (tupleProduct v)) =
      FineDetectorWords.ordinaryPolynomial (tupleColumns B) (fun I => tupleCoefficient B a I.val) z := by
    rw [FineDetectorWords.ordinaryPolynomial, Finset.sum_coe_sort (tupleColumns B)
      (fun I => tupleCoefficient B a I * idealRowHom z I)]
    exact tuple_weighted_regroup B a (idealRowHom z)
  have hmass := tupleCoefficient_square_mass_small_power B a ε X hε hX (word_source_nonzero pools hnz) hN
  have hdom : (∑ v ∈ B, ‖a v‖^2) ≤ ∑ v ∈ B, ‖wordCoefficient c v‖^2 := by
    apply Finset.sum_le_sum; intro v hv; apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    simpa only [a,norm_mul,one_mul] using mul_le_mul_of_nonneg_right (hm v hv) (norm_nonneg (wordCoefficient c v))
  have hp := Finset.prod_le_prod₀ (s:=Finset.univ) (fun (i : Fin r) _ => Finset.sum_nonneg (fun I (_ : I ∈ pools i) => sq_nonneg ‖c i I‖)) (fun i _ => hc i)
  rw [show B = wordTuples pools from rfl, word_unmerged_square_mass] at hdom
  have hd := mul_nonneg (wordDivisorConstant_pos r ε hε).le (Real.rpow_nonneg (zero_le_one.trans hX) ε)
  have hh := hmass.trans (mul_le_mul_of_nonneg_left (hdom.trans hp) hd)
  rw [Finset.sum_coe_sort (tupleColumns B) (fun I => ‖tupleCoefficient B a I‖^2)] at hcols
  change (∑ z : rows, ‖∑ v ∈ B, a v * idealRowHom z.val (tupleProduct v)‖^2) ≤ _
  simp_rw [hsum]; exact hcols.trans (mul_le_mul_of_nonneg_left hh hK)

#print axioms masked_word_energy
end
end QRH.Cycle092.MergedColumn
