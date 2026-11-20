/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Expose the genuine source height/logarithmic prefactor before finite Cauchy. -/
import Candidate.C092.transport.MixedMiddleReturnRows

set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section

lemma source_energy_power {U A Cs window epsilon loss d : ℝ}
    (hU : 1<U) (hA : 0≤A) (hCs : 0≤Cs) (hw : 0≤window)
    (he : 0≤epsilon) (hl : 0≤loss) :
    U^(-d)*(Cs*(U^loss*window*(A*U^(1+epsilon))+1)) ≤
      max 1 (Cs*(window*A+1))*U^(1+(epsilon+loss-d)) := by
  have hup : 0<U := zero_lt_one.trans hU
  have hp : 1≤U^(1+epsilon+loss) := Real.one_le_rpow hU.le (by linarith)
  have hh : Cs*(U^loss*window*(A*U^(1+epsilon))+1) ≤
      Cs*(window*A+1)*U^(1+epsilon+loss) := by
    have hh : U^loss*window*(A*U^(1+epsilon))+1 ≤
        U^loss*window*(A*U^(1+epsilon))+U^(1+epsilon+loss) := by linarith only [hp]
    apply (mul_le_mul_of_nonneg_left hh hCs).trans_eq
    have hr : U^loss*U^(1+epsilon)=U^(1+epsilon+loss) := by
      rw [←Real.rpow_add hup];congr 1;ring
    rw [←hr]
    ring
  calc
    _ ≤ U^(-d)*((Cs*(window*A+1))*U^(1+epsilon+loss)) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hup.le _)
    _ = Cs*(window*A+1)*U^(1+(epsilon+loss-d)) := by
      rw [mul_left_comm,←Real.rpow_add hup]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hup.le _)

#print axioms source_energy_power
end
end QRH.Cycle092.MixedMiddleReturn
