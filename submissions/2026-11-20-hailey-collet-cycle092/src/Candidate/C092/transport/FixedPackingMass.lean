/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The harmonic sum over the artificial second divisor in H.16 is independent
of the packed row. Only the genuine code factors are bounded by its divisors. -/
import Candidate.C092.transport.SixthCore
import Candidate.C092.transport.FixedAllocationWeight

namespace QRH.Cycle092.FixedAllocationWeight
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeInverseAmplification IdealMobiusDivisorSum
open LocalMoment ProbePhysical Record12518109GainRoot
local notation "NZ" => HeckeInverseAmplification.NonzeroIdeal
local notation "O" => HeckeFamily.O

theorem harmonic_cutoff (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U → ∀ S : Finset NZ,
      (∀ I ∈ S, (I.val.absNorm:ℝ) ≤ U^L) →
      (∑ I ∈ S,(I.val.absNorm:ℝ)⁻¹) ≤ C*U^ε := by
  let δ := ε/(1+L)
  have hd : 0 < δ := div_pos hε (by linarith)
  have hid : δ*(1+L)=ε := div_mul_cancel₀ _ (by linarith)
  let w : NZ → ℝ := fun I => (I.val.absNorm:ℝ)^(-6*((1+δ)/6))
  have hs : Summable w := ideal_sixth_power_summable ((1+δ)/6) (by linarith)
  have hw (I : NZ) : 0 ≤ w I := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hn : 0 ≤ ∑' I,w I := tsum_nonneg hw
  refine ⟨(∑' I,w I)+1,by linarith,?_⟩; intro U hU S hcap
  have hUp := zero_lt_one.trans_le hU
  have hterm (I : NZ) (hI : I∈S) : (I.val.absNorm:ℝ)⁻¹ ≤ w I*U^ε := by
    have hN : 0 < (I.val.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
    have hpow := Real.rpow_le_rpow hN.le (hcap I hI) hd.le
    rw [←Real.rpow_mul hUp.le] at hpow
    have hpow' := hpow.trans (Real.rpow_le_rpow_of_exponent_le hU (by nlinarith only [hid,hd] : L*δ ≤ ε))
    calc
      _ = w I*(I.val.absNorm:ℝ)^δ := by
        dsimp [w]; rw [←Real.rpow_add hN,show -6*((1+δ)/6)+δ=(-1:ℝ) by ring,Real.rpow_neg_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow' (hw I)
  calc
    _ ≤ ∑ I ∈ S,w I*U^ε := Finset.sum_le_sum hterm
    _ = (∑ I ∈ S,w I)*U^ε := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right ((hs.sum_le_tsum S (fun I _ => hw I)).trans (by linarith)) (Real.rpow_nonneg hUp.le _)

theorem original_H16 (Y L ε : ℝ) (hY : 0 ≤ Y) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U → ∀ y : O, y ≠ 0 → ((Ideal.span {y}).absNorm:ℝ) ≤ U^Y →
      ∀ S : Finset NZ, (∀ I ∈ S,(I.val.absNorm:ℝ) ≤ U^L) →
      ((idealDivisors ((Ideal.span {y})^2)).card:ℝ)^3 *
        (∑ I ∈ S,(I.val.absNorm:ℝ)⁻¹) ≤ C*U^ε := by
  obtain ⟨A,hA,ha⟩ := CenteredMomentMask.polynomial_mask_divisor_bound (ε/6) (Y*2) (by positivity) (by positivity)
  obtain ⟨B,hB,hb⟩ := harmonic_cutoff L (ε/2) hL (by positivity)
  refine ⟨A^3*B,by positivity,?_⟩; intro U hU y hy hyU S hS
  have hI : (Ideal.span {y} : Ideal O) ≠ 0 := fun he => hy (Ideal.span_singleton_eq_bot.mp he)
  have hUp := zero_lt_one.trans_le hU
  have hN : (((Ideal.span {y})^2).absNorm:ℝ) ≤ U^(Y*2) := by
    rw [map_pow,Nat.cast_pow,Real.rpow_mul hUp.le,Real.rpow_ofNat]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hyU _
  have hdiv := pow_le_pow_left₀ (by positivity) (ha U hU _ (pow_ne_zero 2 hI) hN) 3
  have harm := hb U hU S hS
  refine (mul_le_mul hdiv harm (Finset.sum_nonneg (fun I _ => by positivity)) (by positivity)).trans_eq ?_
  rw [mul_pow,← Real.rpow_natCast (U^(ε/6)) 3,← Real.rpow_mul hUp.le]
  calc
    _ = A^3*B*(U^(ε/6*(3:ℝ))*U^(ε/2)) := by norm_num only [Nat.cast_ofNat]; ring
    _ = _ := by rw [←Real.rpow_add hUp,show ε/6*(3:ℝ)+ε/2=ε by ring]

#print axioms harmonic_cutoff
#print axioms original_H16
end
end QRH.Cycle092.FixedAllocationWeight
