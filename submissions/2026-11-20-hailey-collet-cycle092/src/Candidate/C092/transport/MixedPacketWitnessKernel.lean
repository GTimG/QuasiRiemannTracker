/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Outer mixed return: saturated ordinary witness plus same-row second moment.
The physical reciprocal remains an independent retained original factor. -/
import Candidate.C092.transport.DirectCountCombined
import Candidate.C092.transport.WitnessRowSupActualP4

set_option autoImplicit false
namespace QRH.Cycle092.MixedPacketWitness
noncomputable section
open scoped Classical BigOperators

/-- A second-moment source pays half the count deficit. The ordinary witness
is retained until its authentic squared lower bound is used. No reciprocal
is evaluated at the auxiliary inverse or ordinary witness. -/
theorem saturated_second_bin {Row : Type*} (rows : Finset Row)
    (numerator ordinary selected full reciprocal : Row→ℂ)
    (U R G total inverse ordinaryLower selectedLower epsilon Ccount Cmoment : ℝ)
    (hU : 0 < U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment)
    (hcard : (rows.card:ℝ) ≤ Ccount*U^(R-G))
    (hordinary : ∀ u∈rows,U^ordinaryLower ≤ ‖ordinary u‖^2)
    (hselected : ∀ u∈rows,U^selectedLower ≤ ‖selected u‖)
    (hfull : ∀ u∈rows,‖full u‖ ≤ U^total)
    (hinverse : ∀ u∈rows,‖reciprocal u‖ ≤ U^inverse)
    (henergy : (∑ u∈rows,‖numerator u*ordinary u*selected u‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ u∈rows,‖numerator u*full u*reciprocal u‖) ≤ Ccount*Cmoment*
      U^(total+inverse-selectedLower-ordinaryLower/2+(R+1+epsilon)/2-G/2) := by
  have hp (e : ℝ) : (U^e)^2 = U^(2*e) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU.le];congr 1;ring
  let L := U^(ordinaryLower/2)*U^selectedLower
  have hL : 0 < L := by dsimp [L];positivity
  have hlo (u : Row) (hu : u∈rows) : L ≤ ‖ordinary u*selected u‖ := by
    have hO : U^(ordinaryLower/2) ≤ ‖ordinary u‖ := by
      apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hU.le _) (norm_nonneg _) (by norm_num : (2:ℕ)≠0)).mp
      simpa only [hp,show 2*(ordinaryLower/2)=ordinaryLower by ring] using hordinary u hu
    rw [norm_mul]
    exact mul_le_mul hO (hselected u hu) (Real.rpow_nonneg hU.le _) (norm_nonneg _)
  have hs : L*(∑ u∈rows,‖numerator u*full u*reciprocal u‖) ≤
      U^(total+inverse)*(∑ u∈rows,‖numerator u*ordinary u*selected u‖) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    have hP : ‖full u*reciprocal u‖ ≤ U^(total+inverse) := by
      rw [norm_mul,Real.rpow_add hU]
      exact mul_le_mul (hfull u hu) (hinverse u hu) (norm_nonneg _) (Real.rpow_nonneg hU.le _)
    simp only [norm_mul] at hP ⊢
    calc
      _ = L*(‖numerator u‖*(‖full u‖*‖reciprocal u‖)) := by ring
      _ ≤ L*(‖numerator u‖*U^(total+inverse)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP (norm_nonneg _)) hL.le
      _ ≤ (‖ordinary u‖*‖selected u‖)*(‖numerator u‖*U^(total+inverse)) := by
        apply mul_le_mul_of_nonneg_right (by simpa only [norm_mul] using hlo u hu) (by positivity)
      _ = _ := by ring
  have hC := Finset.sum_mul_sq_le_sq_mul_sq rows
    (fun u=>‖numerator u*ordinary u*selected u‖) (fun _=>(1:ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hC
  have hCS : (∑ u∈rows,‖numerator u*ordinary u*selected u‖)^2 ≤
      (Ccount*U^(R-G))*(Cmoment*U^(1+epsilon)) := by
    apply hC.trans
    have hE0 : 0 ≤ ∑ u∈rows,‖numerator u*ordinary u*selected u‖^2 := by positivity
    calc
      _ ≤ (Cmoment*U^(1+epsilon))*(Ccount*U^(R-G)) := mul_le_mul henergy hcard (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hconst : Ccount*Cmoment ≤ (Ccount*Cmoment)^2 := by
    have hc0 : 0 ≤ Ccount := by linarith
    have hm0 : 0 ≤ Cmoment := by linarith
    have h : 1 ≤ Ccount*Cmoment := one_le_mul_of_one_le_of_one_le hc hm
    nlinarith
  let E := total+inverse-selectedLower-ordinaryLower/2+(R+1+epsilon)/2-G/2
  have hLE : L*U^E = U^((2*(total+inverse)+(R-G)+1+epsilon)/2) := by
    dsimp [L,E]
    rw [mul_assoc,←Real.rpow_add hU,←Real.rpow_add hU]
    congr 1
    ring
  have htarget : (L*(Ccount*Cmoment*U^E))^2 =
      (Ccount*Cmoment)^2*U^(2*(total+inverse)+(R-G)+1+epsilon) := by
    calc
      _ = (Ccount*Cmoment)^2*(L*U^E)^2 := by ring
      _ = _ := by rw [hLE,hp];congr 2;ring
  have hbound : (L*(∑ u∈rows,‖numerator u*full u*reciprocal u‖))^2 ≤
      (L*(Ccount*Cmoment*U^E))^2 := by
    calc
      _ ≤ (U^(total+inverse)*(∑ u∈rows,‖numerator u*ordinary u*selected u‖))^2 :=
        pow_le_pow_left₀ (by positivity) hs 2
      _ = (U^(total+inverse))^2*(∑ u∈rows,‖numerator u*ordinary u*selected u‖)^2 := mul_pow _ _ _
      _ ≤ (U^(total+inverse))^2*((Ccount*U^(R-G))*(Cmoment*U^(1+epsilon))) :=
        mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
      _ = Ccount*Cmoment*U^(2*(total+inverse)+(R-G)+1+epsilon) := by
        rw [hp]
        calc
          _ = Ccount*Cmoment*((U^(2*(total+inverse))*U^(R-G))*U^(1+epsilon)) := by ring
          _ = _ := by rw [←Real.rpow_add hU,←Real.rpow_add hU];congr 2;ring
      _ ≤ (Ccount*Cmoment)^2*U^(2*(total+inverse)+(R-G)+1+epsilon) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hU.le _)
      _ = _ := htarget.symm
  have h := (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (2:ℕ)≠0)).mp hbound
  exact (mul_le_mul_iff_right₀ hL).mp h

#print axioms saturated_second_bin
end
end QRH.Cycle092.MixedPacketWitness
