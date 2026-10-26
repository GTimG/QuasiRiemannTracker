/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103TwoIdeal.FormalKernel

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103TwoIdeal
noncomputable section

def degree (n : Exponent) : ℕ := n 0+n 1
def inverseCoeff (n : Exponent) : ℤ := MvPowerSeries.coeff n inverseSeries
def shiftedInverseCoeff (n : Exponent) (i j : ℕ) : ℤ :=
  if exponent i j ≤ n then inverseCoeff (n-exponent i j) else 0

theorem formal_power_monomial (i j : ℕ) :
    formalX^i*formalY^j = MvPowerSeries.monomial (exponent i j) 1 := by
  simp only [formalX,formalY,MvPowerSeries.X_pow_eq,
    MvPowerSeries.monomial_mul_monomial,one_mul,exponent]

theorem coeff_shift (n : Exponent) (i j : ℕ) :
    MvPowerSeries.coeff n ((formalX^i*formalY^j)*inverseSeries) =
      shiftedInverseCoeff n i j := by
  rw [formal_power_monomial,MvPowerSeries.coeff_monomial_mul]
  simp only [shiftedInverseCoeff,inverseCoeff,one_mul]

theorem inverse_coefficient_recurrence (n : Exponent) :
    inverseCoeff n-shiftedInverseCoeff n 2 0-shiftedInverseCoeff n 1 1-
        shiftedInverseCoeff n 0 2+shiftedInverseCoeff n 2 1+
        shiftedInverseCoeff n 1 2 = if n=0 then 1 else 0 := by
  have he : forwardSeries*inverseSeries =
      inverseSeries-(formalX^2*formalY^0)*inverseSeries-
        (formalX^1*formalY^1)*inverseSeries-(formalX^0*formalY^2)*inverseSeries+
        (formalX^2*formalY^1)*inverseSeries+(formalX^1*formalY^2)*inverseSeries := by
    unfold forwardSeries squarefreeSeries
    ring
  have h := congrArg (MvPowerSeries.coeff n) forward_inverse
  rw [he] at h
  simpa only [map_add,map_sub,coeff_shift,inverseCoeff,MvPowerSeries.coeff_one] using h

theorem degree_sub_exponent (n : Exponent) (i j : ℕ) (h : exponent i j ≤ n) :
    degree (n-exponent i j) = degree n-(i+j) := by
  obtain ⟨hi,hj⟩ := (exponent_le_iff i j n).mp h
  simp only [degree,Finsupp.coe_tsub,Pi.sub_apply,exponent,Finsupp.coe_add,
    Pi.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne (by decide : (0:Fin 2)≠1),
    Finsupp.single_eq_of_ne (by decide : (1:Fin 2)≠0),zero_add,add_zero]
  omega

theorem inverseCoeff_zero : inverseCoeff 0 = 1 := by
  have h := inverse_coefficient_recurrence 0
  norm_num [shiftedInverseCoeff,exponent] at h
  exact h

theorem inverseCoeff_degree_one (n : Exponent) (hdeg : degree n=1) : inverseCoeff n=0 := by
  have hn : n≠0 := by intro h; simp [h,degree] at hdeg
  have hshift (i j : ℕ) (hij : 2 ≤ i+j) : shiftedInverseCoeff n i j=0 := by
    rw [shiftedInverseCoeff,if_neg]
    intro h
    obtain ⟨hi,hj⟩ := (exponent_le_iff i j n).mp h
    unfold degree at hdeg
    omega
  simpa only [hshift 2 0 (by decide),hshift 1 1 (by decide),hshift 0 2 (by decide),
    hshift 2 1 (by decide),hshift 1 2 (by decide),if_neg hn,sub_zero,add_zero] using
    inverse_coefficient_recurrence n

end
end QRH.Record1252270103TwoIdeal

#print axioms QRH.Record1252270103TwoIdeal.inverse_coefficient_recurrence
#print axioms QRH.Record1252270103TwoIdeal.inverseCoeff_degree_one
