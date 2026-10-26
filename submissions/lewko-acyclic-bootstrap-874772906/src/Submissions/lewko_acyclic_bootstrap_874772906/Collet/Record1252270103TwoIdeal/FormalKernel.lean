/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Exact local two-variable divisor convolution and its integral inverse. -/
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103TwoIdeal
noncomputable section
open scoped BigOperators

abbrev Exponent := Fin 2 →₀ ℕ
abbrev LocalSeries := MvPowerSeries (Fin 2) ℤ

def exponent (i j : ℕ) : Exponent := Finsupp.single 0 i + Finsupp.single 1 j
def formalX : LocalSeries := MvPowerSeries.X 0
def formalY : LocalSeries := MvPowerSeries.X 1
def ordinarySeries : LocalSeries := fun _ => 1
def squarefreeSeries : LocalSeries := 1+formalX+formalY
def forwardSeries : LocalSeries := (1-formalX)*(1-formalY)*squarefreeSeries
def inverseSeries : LocalSeries := MvPowerSeries.invOfUnit forwardSeries 1

theorem exponent_le_iff (i j : ℕ) (n : Exponent) :
    exponent i j ≤ n ↔ i ≤ n 0 ∧ j ≤ n 1 := by
  constructor
  · intro h
    exact ⟨by simpa [exponent] using h 0, by simpa [exponent] using h 1⟩
  · rintro ⟨hi,hj⟩ k
    fin_cases k
    · simpa [exponent] using hi
    · simpa [exponent] using hj

theorem exponent_zero_iff (n : Exponent) : n = 0 ↔ n 0 = 0 ∧ n 1 = 0 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0,h1⟩
    ext k
    fin_cases k
    · simpa using h0
    · simpa using h1

theorem formalXY_monomial : formalX*formalY = MvPowerSeries.monomial (exponent 1 1) 1 := by
  simp only [formalX,formalY,MvPowerSeries.X_def,MvPowerSeries.monomial_mul_monomial,
    one_mul,exponent]

theorem coeff_ordinarySeries (n : Exponent) : MvPowerSeries.coeff n ordinarySeries = 1 := rfl

theorem ordinary_geometric_identity : (1-formalX)*(1-formalY)*ordinarySeries = 1 := by
  have hexp : (1-formalX)*(1-formalY)*ordinarySeries =
      ordinarySeries-formalX*ordinarySeries-formalY*ordinarySeries+
        (formalX*formalY)*ordinarySeries := by ring
  rw [hexp,formalXY_monomial]
  ext n
  simp only [map_add,map_sub,coeff_ordinarySeries,
    formalX,formalY,MvPowerSeries.X_def,MvPowerSeries.coeff_monomial_mul,
    coeff_ordinarySeries,one_mul,MvPowerSeries.coeff_one,Finsupp.single_le_iff,
    exponent_le_iff,exponent_zero_iff]
  by_cases h0 : n 0 = 0 <;> by_cases h1 : n 1 = 0 <;>
    simp [h0,h1,Nat.one_le_iff_ne_zero]

theorem forward_divisor_identity : forwardSeries*ordinarySeries = squarefreeSeries := by
  calc
    forwardSeries*ordinarySeries = squarefreeSeries*((1-formalX)*(1-formalY)*ordinarySeries) := by
      unfold forwardSeries
      ring
    _ = squarefreeSeries := by rw [ordinary_geometric_identity,mul_one]

theorem forward_constant : MvPowerSeries.constantCoeff forwardSeries = 1 := by
  simp [forwardSeries,squarefreeSeries,formalX,formalY,MvPowerSeries.constantCoeff_X]

theorem forward_inverse : forwardSeries*inverseSeries = 1 :=
  MvPowerSeries.mul_invOfUnit forwardSeries 1 forward_constant

theorem inverse_forward : inverseSeries*forwardSeries = 1 :=
  MvPowerSeries.invOfUnit_mul forwardSeries 1 forward_constant

theorem inverse_divisor_identity : inverseSeries*squarefreeSeries = ordinarySeries := by
  calc
    inverseSeries*squarefreeSeries = inverseSeries*(forwardSeries*ordinarySeries) := by
      rw [forward_divisor_identity]
    _ = (inverseSeries*forwardSeries)*ordinarySeries := (mul_assoc _ _ _).symm
    _ = ordinarySeries := by rw [inverse_forward,one_mul]

/-- Finite exact convolution coefficient, including every valuation pair. -/
theorem forward_coefficient_identity (n : Exponent) :
    ∑ d ∈ Finset.antidiagonal n, MvPowerSeries.coeff d.1 forwardSeries *
        MvPowerSeries.coeff d.2 ordinarySeries = MvPowerSeries.coeff n squarefreeSeries := by
  rw [← MvPowerSeries.coeff_mul,forward_divisor_identity]

theorem inverse_coefficient_identity (n : Exponent) :
    ∑ d ∈ Finset.antidiagonal n, MvPowerSeries.coeff d.1 inverseSeries *
        MvPowerSeries.coeff d.2 squarefreeSeries = 1 := by
  rw [← MvPowerSeries.coeff_mul,inverse_divisor_identity,coeff_ordinarySeries]

end
end QRH.Record1252270103TwoIdeal

#print axioms QRH.Record1252270103TwoIdeal.ordinary_geometric_identity
#print axioms QRH.Record1252270103TwoIdeal.forward_coefficient_identity
#print axioms QRH.Record1252270103TwoIdeal.inverse_coefficient_identity
