/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Combine the ordinary H8 payment at qOrd with the genuinely frozen prime
weights, keeping both original volume factors and the true shortened scales. -/
import Candidate.C092.transport.FixedMarkedVolume
import Candidate.C092.transport.H8ProfileUniform

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.SignedCenter
namespace QRH.Cycle092.FixedAllocationWeight
local notation "O" => HeckeFamily.O

theorem paid_marked_square {w x : ℂ} {C B P T L qOrd qMark q₀ : ℝ}
    (hT : 0≤T) (hP : 0≤P) (ho : 0 < qOrd) (hm : 1 ≤ qMark) (hq : 0<q₀)
    (hprod : q₀ ≤ qOrd*qMark)
    (hordinary : ‖x‖^2 ≤ C^2*T*(qOrd*max 1 L)⁻¹)
    (hmarks : ‖w‖^2 ≤ B^2*P*qMark⁻¹^2) :
    ‖w*x‖^2 ≤ (B*C)^2*(T*P)*(q₀*max 1 L)⁻¹ := by
  have hM := zero_lt_one.trans_le hm
  have hLf : 0 < max 1 L := zero_lt_one.trans_le (le_max_left _ _)
  have hq' : q₀ ≤ qOrd*qMark^2 := hprod.trans (mul_le_mul_of_nonneg_left (by nlinarith only [mul_nonneg hM.le (sub_nonneg.mpr hm)]) ho.le)
  have hrec := (inv_le_inv₀ (mul_pos (mul_pos ho (sq_pos_of_pos hM)) hLf) (mul_pos hq hLf)).mpr
    (mul_le_mul_of_nonneg_right hq' hLf.le)
  rw [norm_mul,mul_pow]
  calc
    _ ≤ (B^2*P*qMark⁻¹^2)*(C^2*T*(qOrd*max 1 L)⁻¹) :=
      mul_le_mul hmarks hordinary (sq_nonneg _) (by positivity)
    _ = (B*C)^2*(T*P)*(qOrd*qMark^2*max 1 L)⁻¹ := by simp only [mul_inv,inv_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by positivity)

theorem all_mark_factors {ι : Type*} [Fintype ι] (q P A : ι→ℝ)
    (hP : ∀ i,0<P i) (hq : ∀ i, 0 < q i)
    (hcap : ∀ i, q i ≠ 1 → q i ≤ 2*P i) :
    (∏ i, if q i=1 then (A i)^2*P i else (A i)^2/P i) ≤
      (∏ i,(2*A i)^2)*(∏ i,P i)*(∏ i,q i)⁻¹^2 := by
  calc
    _ ≤ ∏ i,(2*A i)^2*P i*(q i)⁻¹^2 := by
      apply Finset.prod_le_prod₀
      · intro i _; split_ifs <;> first | exact mul_nonneg (sq_nonneg _) (hP i).le | exact div_nonneg (sq_nonneg _) (hP i).le
      · intro i _
        by_cases h : q i=1
        · simp only [h,ite_true,inv_one,one_pow,mul_one]
          exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (A i)]) (hP i).le
        · rw [if_neg h];exact forced_slot_factor (hP i) (hq i) (hcap i h)
    _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_pow,Finset.prod_inv_distrib]

#print axioms paid_marked_square
#print axioms all_mark_factors
end QRH.Cycle092.FixedAllocationWeight
end
