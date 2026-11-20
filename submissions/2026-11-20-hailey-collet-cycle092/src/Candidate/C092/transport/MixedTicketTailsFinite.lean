/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Full genuine coefficient-dilation bank with its strict quarter-density tail
payment. Finite coefficient bins preserve original terms and actual source shift. -/
import Candidate.C092.transport.MixedTicketTailsDamping
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
namespace QRH.Cycle092.MixedTicketTails

theorem finite_large_bins {ι : Type*} (rows : Finset ι) (n : ℕ)
    (S Q : ℕ→ι→ℂ) (P f : ι→ℂ)
    (y cost d U R q L xi ann delta loss epsilon Ccount Cmoment M vcut : ℝ)
    (hcost : 0 ≤ cost) (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hM : 0 ≤ M)
    (hq : 0 ≤ q) (hqd : q ≤ delta/2) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hcard : (rows.card:ℝ) ≤ Ccount*U^R)
    (hsplit : ∀i∈rows,f i=∑j∈Finset.range (n+1),
      ((M*U^(-delta*((j:ℝ)*xi)/2):ℝ):ℂ)*S j i)
    (hselected : ∀j∈Finset.range (n+1),∀i∈rows,U^(q*
      Physical.Selection.scheduledCapacity y cost d (2*((j:ℝ)*xi+xi+ann))-loss) ≤ ‖Q j i‖)
    (hfull : ∀i∈rows,‖P i‖ ≤ U^(q*L))
    (henergy : ∀j∈Finset.range (n+1),(∑i∈rows,‖S j i‖^4*‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon))
    (hsmall : ∀j∈Finset.range (n+1),(j:ℝ)*xi+xi<vcut → ∀i∈rows,S j i=0) :
    (∑i∈rows,‖f i*P i‖) ≤ ((n+1:ℕ):ℝ)*M*Ccount*Cmoment*
      U^(q*L-q*Physical.Selection.zeroCapacity y cost d/2+
        (3*R+1+epsilon)/4+loss/2+delta*(2*xi+ann)/4-delta*vcut/4) := by
  have hU0 : 0<U := zero_lt_one.trans_le hU
  have hdelta : 0 ≤ delta := by linarith
  let E := q*L-q*Physical.Selection.zeroCapacity y cost d/2+
    (3*R+1+epsilon)/4+loss/2+delta*(2*xi+ann)/4-delta*vcut/4
  have hj (j:ℕ) (hj:j∈Finset.range (n+1)) :
      (∑i∈rows,‖(((M*U^(-delta*((j:ℝ)*xi)/2):ℝ):ℂ)*S j i)*P i‖) ≤ M*Ccount*Cmoment*U^E := by
    by_cases hs : (j:ℝ)*xi+xi<vcut
    · have hz : (∑i∈rows,‖(((M*U^(-delta*((j:ℝ)*xi)/2):ℝ):ℂ)*S j i)*P i‖)=0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hsmall j hj hs i hi]
        simp
      rw [hz]
      positivity
    have hg : vcut ≤ (j:ℝ)*xi+xi := le_of_not_gt hs
    have hb := weighted_bin_quarter rows (S j) (Q j) P y cost d U R q L ((j:ℝ)*xi)
      xi ann delta loss epsilon Ccount Cmoment hcost hU hc hm hq hqd
      (by positivity) hxi hann hcard (hselected j hj) hfull (henergy j hj)
    have hpow : U^(q*L-q*Physical.Selection.zeroCapacity y cost d/2+
        (3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/4-delta*((j:ℝ)*xi)/4) ≤ U^E := by
      apply Real.rpow_le_rpow_of_exponent_le hU
      dsimp [E]
      nlinarith [mul_le_mul_of_nonneg_left hg hdelta]
    calc
      _ = M*(U^(-delta*((j:ℝ)*xi)/2)*(∑i∈rows,‖S j i*P i‖)) := by
        rw [Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_assoc,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ M*U^(-delta*((j:ℝ)*xi)/2))]
        ring
      _ ≤ M*(Ccount*Cmoment*U^(q*L-q*Physical.Selection.zeroCapacity y cost d/2+
        (3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/4-delta*((j:ℝ)*xi)/4)) :=
        mul_le_mul_of_nonneg_left hb hM
      _ ≤ M*(Ccount*Cmoment*U^E) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑i∈rows,∑j∈Finset.range (n+1),‖(((M*U^(-delta*((j:ℝ)*xi)/2):ℝ):ℂ)*S j i)*P i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hsplit i hi,Finset.sum_mul]
      exact norm_sum_le _ _
    _ = ∑j∈Finset.range (n+1),∑i∈rows,‖(((M*U^(-delta*((j:ℝ)*xi)/2):ℝ):ℂ)*S j i)*P i‖ := Finset.sum_comm
    _ ≤ ∑j∈Finset.range (n+1),M*Ccount*Cmoment*U^E := Finset.sum_le_sum hj
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul];dsimp [E];ring

#print axioms finite_large_bins
end QRH.Cycle092.MixedTicketTails
