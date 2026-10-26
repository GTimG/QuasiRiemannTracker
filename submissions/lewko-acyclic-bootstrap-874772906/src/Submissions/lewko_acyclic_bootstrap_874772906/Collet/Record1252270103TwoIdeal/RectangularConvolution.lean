/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103TwoIdeal.LocalValuations

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103TwoIdeal
noncomputable section
open scoped BigOperators

theorem rectangular_antidiagonal_sum (a b : ℕ) (f : Exponent → Exponent → ℤ) :
    (∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1),
      f (exponent i j) (exponent (a-i) (b-j))) =
        ∑ d ∈ Finset.antidiagonal (exponent a b), f d.1 d.2 := by
  classical
  suffices hs : (∑ ij ∈ Finset.range (a+1) ×ˢ Finset.range (b+1),
      f (exponent ij.1 ij.2) (exponent (a-ij.1) (b-ij.2))) =
        ∑ d ∈ Finset.antidiagonal (exponent a b), f d.1 d.2 by
    simpa only [Finset.sum_product] using hs
  refine Finset.sum_bij
    (fun ij _ => (exponent ij.1 ij.2,exponent (a-ij.1) (b-ij.2))) ?_ ?_ ?_ ?_
  · intro ij hij
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
    have hi' : ij.1 ≤ a := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hj' : ij.2 ≤ b := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    apply Finset.mem_antidiagonal.mpr
    ext k
    fin_cases k <;> simp [exponent,Nat.add_sub_of_le hi',Nat.add_sub_of_le hj']
  · intro x hx y hy he
    have hfirst := congrArg Prod.fst he
    have hcoords := exponent_injective.mp hfirst
    exact Prod.ext hcoords.1 hcoords.2
  · intro d hd
    have he := Finset.mem_antidiagonal.mp hd
    have h0 := congrArg (fun n : Exponent => n 0) he
    have h1 := congrArg (fun n : Exponent => n 1) he
    simp only [Finsupp.add_apply,exponent,Finsupp.coe_add,Pi.add_apply,
      Finsupp.single_eq_same,Finsupp.single_eq_of_ne (by decide : (1:Fin 2)≠0),
      Finsupp.single_eq_of_ne (by decide : (0:Fin 2)≠1),add_zero,zero_add] at h0 h1
    refine ⟨(d.1 0,d.1 1),?_,?_⟩
    · simp only [Finset.mem_product,Finset.mem_range]
      omega
    · apply Prod.ext
      · exact exponent_reconstruct d.1
      · ext k
        fin_cases k <;> simp [exponent] <;> omega
  · intro ij hij
    rfl

theorem forward_rectangular_convolution (a b : ℕ) :
    (∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1),
      forwardCoeff (exponent i j)) = if a+b ≤ 1 then 1 else 0 := by
  have h := forward_coefficient_identity (exponent a b)
  rw [squarefree_coefficient_at] at h
  rw [← rectangular_antidiagonal_sum a b
    (fun x y => MvPowerSeries.coeff x forwardSeries*MvPowerSeries.coeff y ordinarySeries)] at h
  simpa only [coeff_ordinarySeries,mul_one,forwardCoeff] using h

theorem inverse_rectangular_convolution (a b : ℕ) :
    (∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1),
      inverseCoeff (exponent i j)*(if (a-i)+(b-j) ≤ 1 then 1 else 0)) = 1 := by
  have h := inverse_coefficient_identity (exponent a b)
  rw [← rectangular_antidiagonal_sum a b
    (fun x y => MvPowerSeries.coeff x inverseSeries*MvPowerSeries.coeff y squarefreeSeries)] at h
  simpa only [inverseCoeff,squarefree_coefficient_at] using h

end
end QRH.Record1252270103TwoIdeal

#print axioms QRH.Record1252270103TwoIdeal.forward_rectangular_convolution
#print axioms QRH.Record1252270103TwoIdeal.inverse_rectangular_convolution
