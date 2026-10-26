/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103TwoIdeal.LocalValuations
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103TwoIdeal
noncomputable section
open scoped BigOperators

def forwardLocalMass (z : ℝ) (ij : ℕ×ℕ) : ℝ :=
  |(forwardCoeff (exponent ij.1 ij.2) : ℝ)| * z^(ij.1+ij.2)

def pointMass (z : ℝ) (a b : ℕ) (ij : ℕ×ℕ) : ℝ :=
  if ij=(a,b) then z^(a+b) else 0

theorem forwardLocalMass_points (z : ℝ) (ij : ℕ×ℕ) :
    forwardLocalMass z ij = pointMass z 0 0 ij+pointMass z 2 0 ij+
      pointMass z 1 1 ij+pointMass z 0 2 ij+pointMass z 2 1 ij+pointMass z 1 2 ij := by
  rcases ij with ⟨i,j⟩
  unfold forwardLocalMass pointMass
  rw [forward_coefficient_at]
  simp only [Prod.mk.injEq,Int.cast_add,Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero]
  by_cases hi : i ≤ 2
  · by_cases hj : j ≤ 2
    · interval_cases i <;> interval_cases j <;> norm_num
    · have h0 : j ≠ 0 := by omega
      have h1 : j ≠ 1 := by omega
      have h2 : j ≠ 2 := by omega
      simp [h0,h1,h2]
  · have h0 : i ≠ 0 := by omega
    have h1 : i ≠ 1 := by omega
    have h2 : i ≠ 2 := by omega
    simp [h0,h1,h2]

theorem forwardLocalMass_hasSum (z : ℝ) :
    HasSum (forwardLocalMass z) (1+3*z^2+2*z^3) := by
  have hp (a b : ℕ) : HasSum (pointMass z a b) (z^(a+b)) := by
    exact hasSum_ite_eq (a,b) (z^(a+b))
  have hs := (((((hp 0 0).add (hp 2 0)).add (hp 1 1)).add (hp 0 2)).add (hp 2 1)).add (hp 1 2)
  convert hs using 1
  · funext ij
    exact forwardLocalMass_points z ij
  · ring

theorem forwardLocalMass_finite (T : Finset (ℕ×ℕ)) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∑ ij ∈ T, forwardLocalMass z ij ≤ 1+5*z^2 := by
  have hn (ij : ℕ×ℕ) : 0 ≤ forwardLocalMass z ij :=
    mul_nonneg (abs_nonneg _) (pow_nonneg hz _)
  have hs := (forwardLocalMass_hasSum z).summable.sum_le_tsum T (fun ij _ => hn ij)
  rw [(forwardLocalMass_hasSum z).tsum_eq] at hs
  have hpow : z^3 ≤ z^2 := by nlinarith [sq_nonneg z,mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz1)]
  linarith

end
end QRH.Record1252270103TwoIdeal

#print axioms QRH.Record1252270103TwoIdeal.forwardLocalMass_hasSum
#print axioms QRH.Record1252270103TwoIdeal.forwardLocalMass_finite
