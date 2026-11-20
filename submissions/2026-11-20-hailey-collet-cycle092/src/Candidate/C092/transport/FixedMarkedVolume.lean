/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The ordinary shortening and the marked allocation pay in different places.
Combine them only after retaining the original-volume normalizer. -/
import Candidate.C092.transport.FixedAllocationWeight
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
namespace QRH.Cycle092.FixedAllocationWeight

theorem forced_slot_factor {P N A : ℝ} (hP : 0<P) (hN : 0<N) (hcap : N ≤ 2*P) :
    A^2/P ≤ (2*A)^2*P*N⁻¹^2 := by
  have hh := pow_le_pow_left₀ hN.le hcap 2
  apply (div_le_iff₀ hP).2
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_left hh (sq_nonneg A)]

/-- This form charges the square of the frozen scalar at each marked
coordinate, leaving a factor P/N² against the original volume. -/
theorem frozen_product_factor {ι : Type*} [DecidableEq ι] (s : Finset ι) (P N A : ι→ℝ)
    (hP : ∀ i∈s,0<P i) (hN : ∀ i∈s,0<N i) (hcap : ∀ i∈s,N i≤2*P i) :
    (∏ i∈s,(A i)^2/P i) ≤ (∏ i∈s,(2*A i)^2) * (∏ i∈s,P i) * (∏ i∈s,N i)⁻¹^2 := by
  calc
    _ ≤ ∏ i∈s,(2*A i)^2*P i*(N i)⁻¹^2 := Finset.prod_le_prod₀
      (fun i hi => div_nonneg (sq_nonneg _) (hP i hi).le)
      (fun i hi => forced_slot_factor (hP i hi) (hN i hi) (hcap i hi))
    _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_pow,Finset.prod_inv_distrib]

/-- H8 is evaluated at T/qOrd. The marked scalar contributes qMark^{-1}.
The full q=qOrd*qMark enters H14 and does not replace the shortened
ordinary rectangle length in H8. -/
theorem combined_squared {raw marks : ℂ} {T P qOrd qMark q₀ L C B : ℝ}
    (hT : 0<T) (hP : 0<P) (hOrd : 1≤qOrd) (hMark : 1≤qMark)
    (h₀ : 1≤q₀) (hprod : q₀ ≤ qOrd*qMark) (hL : 0≤L) (hC : 0≤C)
    (hraw : ‖(Real.sqrt (T/qOrd):ℂ)⁻¹*raw‖ ≤ C*Real.sqrt (T/qOrd)*(max 1 (L/qOrd))^(-(3/5):ℝ))
    (hmarks : ‖marks‖^2 ≤ B^2*P*qMark⁻¹^2) :
    ‖marks*((Real.sqrt T:ℂ)⁻¹*raw)‖^2 ≤ (B*C)^2*(T*P)*(q₀*max 1 L)⁻¹ := by
  have ho := zero_lt_one.trans_le hOrd
  have hm := zero_lt_one.trans_le hMark
  have hX := div_pos hT ho
  let M := max 1 (L/qOrd)
  let M' := max 1 (L/(qOrd*qMark))
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  have hM' : 0 < M' := zero_lt_one.trans_le (le_max_left _ _)
  have hcmp : M'≤M := max_le_max_left _ (div_le_div_of_nonneg_left hL ho
    (le_mul_of_one_le_right ho.le hMark))
  have ha : ‖raw‖≤C*(T/qOrd)*M^(-(3/5):ℝ) := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),←div_eq_inv_mul] at hraw
    have h := (div_le_iff₀ (Real.sqrt_pos.mpr hX)).mp hraw
    refine h.trans_eq ?_
    calc
      _ = C*(Real.sqrt (T/qOrd))^2*M^(-(3/5):ℝ) := by dsimp only [M]; ring
      _ = _ := by rw [Real.sq_sqrt hX.le]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have he : (M^(-(3/5):ℝ))^2=M^(-(6/5):ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hM.le]; norm_num
  have hbound := squared_cancellation (L:=L) h₀ hprod
  have hsm : M^(-(6/5):ℝ) ≤ M'^(-(6/5):ℝ) := by
    rw [Real.rpow_neg hM.le, Real.rpow_neg hM'.le]
    exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr (Real.rpow_le_rpow hM'.le hcmp (by norm_num))
  rw [norm_mul,mul_pow,CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hT]
  calc
    _ ≤ (B^2*P*qMark⁻¹^2)*((C*(T/qOrd)*M^(-(3/5):ℝ))^2/T) :=
      mul_le_mul hmarks (div_le_div_of_nonneg_right hsq hT.le) (div_nonneg (sq_nonneg _) hT.le) (by positivity)
    _ = (B*C)^2*(T*P)*((qOrd*qMark)⁻¹^2*M^(-(6/5):ℝ)) := by
      rw [mul_pow (C*(T/qOrd)),he]; field_simp <;> ring
    _ ≤ (B*C)^2*(T*P)*((qOrd*qMark)⁻¹^2*M'^(-(6/5):ℝ)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

#print axioms combined_squared
end QRH.Cycle092.FixedAllocationWeight
end
