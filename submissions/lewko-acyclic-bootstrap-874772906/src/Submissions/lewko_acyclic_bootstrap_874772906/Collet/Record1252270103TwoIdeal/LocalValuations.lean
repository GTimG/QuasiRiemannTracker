/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103TwoIdeal.KernelCoefficients

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103TwoIdeal
noncomputable section

theorem exponent_injective {i j a b : ℕ} :
    exponent i j=exponent a b ↔ i=a ∧ j=b := by
  constructor
  · intro h
    have h0 := congrArg (fun n : Exponent => n 0) h
    have h1 := congrArg (fun n : Exponent => n 1) h
    simpa [exponent] using And.intro h0 h1
  · rintro ⟨rfl,rfl⟩
    rfl

theorem exponent_reconstruct (n : Exponent) : exponent (n 0) (n 1)=n := by
  ext k
  fin_cases k <;> simp [exponent]

theorem exponent_eq_zero (i j : ℕ) : exponent i j=0 ↔ i=0 ∧ j=0 := by
  rw [exponent_zero_iff]
  simp [exponent]

theorem coeff_monomial_at (i j a b : ℕ) :
    MvPowerSeries.coeff (exponent i j) (MvPowerSeries.monomial (exponent a b) (1:ℤ)) =
      if i=a ∧ j=b then 1 else 0 := by
  rw [MvPowerSeries.coeff_monomial]
  simp only [exponent_injective]

theorem squarefree_coefficient_at (i j : ℕ) :
    MvPowerSeries.coeff (exponent i j) squarefreeSeries =
      if i+j ≤ 1 then 1 else 0 := by
  have hx : formalX = MvPowerSeries.monomial (exponent 1 0) 1 := by
    simpa using formal_power_monomial 1 0
  have hy : formalY = MvPowerSeries.monomial (exponent 0 1) 1 := by
    simpa using formal_power_monomial 0 1
  rw [squarefreeSeries,map_add,map_add,hx,hy]
  simp only [MvPowerSeries.coeff_one,exponent_eq_zero,coeff_monomial_at]
  split_ifs <;> omega

def forwardCoeff (n : Exponent) : ℤ := MvPowerSeries.coeff n forwardSeries

theorem forward_coefficient_at (i j : ℕ) :
    forwardCoeff (exponent i j) =
      (if i=0 ∧ j=0 then 1 else 0) -
      (if i=2 ∧ j=0 then 1 else 0) -
      (if i=1 ∧ j=1 then 1 else 0) -
      (if i=0 ∧ j=2 then 1 else 0) +
      (if i=2 ∧ j=1 then 1 else 0) +
      (if i=1 ∧ j=2 then 1 else 0) := by
  have he : forwardSeries = 1-(formalX^2*formalY^0)-(formalX^1*formalY^1)-
      (formalX^0*formalY^2)+(formalX^2*formalY^1)+(formalX^1*formalY^2) := by
    unfold forwardSeries squarefreeSeries
    ring
  simp only [forwardCoeff,he,map_add,map_sub,MvPowerSeries.coeff_one,exponent_eq_zero,
    formal_power_monomial,coeff_monomial_at]

end
end QRH.Record1252270103TwoIdeal

#print axioms QRH.Record1252270103TwoIdeal.squarefree_coefficient_at
#print axioms QRH.Record1252270103TwoIdeal.forward_coefficient_at
