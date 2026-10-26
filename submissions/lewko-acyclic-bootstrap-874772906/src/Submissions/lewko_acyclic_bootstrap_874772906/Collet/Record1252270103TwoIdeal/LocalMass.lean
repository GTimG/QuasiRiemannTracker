/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103TwoIdeal.CoefficientBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103TwoIdeal
noncomputable section
open scoped BigOperators

def inverseLocalMass (z : ℝ) (ij : ℕ × ℕ) : ℝ :=
  |(inverseCoeff (exponent ij.1 ij.2) : ℝ)| * z^(ij.1+ij.2)

theorem degree_exponent (i j : ℕ) : degree (exponent i j) = i+j := by
  simp [degree,exponent]

theorem inverseLocalMass_nonneg {z : ℝ} (hz : 0 ≤ z) (ij : ℕ × ℕ) :
    0 ≤ inverseLocalMass z ij := mul_nonneg (abs_nonneg _) (pow_nonneg hz _)

theorem inverseLocalMass_le_geometric {z : ℝ} (hz : 0 ≤ z) (ij : ℕ × ℕ) :
    inverseLocalMass z ij ≤ (3*z)^(ij.1+ij.2) := by
  unfold inverseLocalMass
  calc
    _ ≤ 3^(ij.1+ij.2)*z^(ij.1+ij.2) :=
      mul_le_mul_of_nonneg_right (by simpa [degree_exponent] using
        (inverseCoeff_abs_bound (exponent ij.1 ij.2))) (pow_nonneg hz _)
    _ = _ := (mul_pow _ _ _).symm

theorem geometric_pair_sum {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun ij : ℕ×ℕ => r^(ij.1+ij.2)) ∧
      (∑' ij : ℕ×ℕ, r^(ij.1+ij.2)) = ((1-r)⁻¹)^2 := by
  have hs := summable_geometric_of_lt_one hr hr1
  have hp := hs.mul_of_nonneg hs (fun n => pow_nonneg hr n) (fun n => pow_nonneg hr n)
  have he := hs.tsum_mul_tsum hs hp
  rw [tsum_geometric_of_lt_one hr hr1] at he
  constructor
  · simpa only [pow_add] using hp
  · simpa only [pow_add,pow_two] using he.symm

theorem inverseLocalMass_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1/4) :
    Summable (inverseLocalMass z) := by
  have hr : 0 ≤ 3*z := by positivity
  have hr1 : 3*z < 1 := by linarith
  exact Summable.of_nonneg_of_le (inverseLocalMass_nonneg hz)
    (inverseLocalMass_le_geometric hz) (geometric_pair_sum hr hr1).1

theorem inverseLocalMass_total {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1/4) :
    (∑' ij : ℕ×ℕ, inverseLocalMass z ij) ≤ 1+432*z^2 := by
  let r := 3*z
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrq : r ≤ 3/4 := by dsimp [r]; linarith
  have hr1 : r < 1 := by linarith
  let g : ℕ×ℕ → ℝ := fun ij => r^(ij.1+ij.2)
  let a : ℕ×ℕ → ℝ := fun ij => if ij=(0,1) then r else 0
  let b : ℕ×ℕ → ℝ := fun ij => if ij=(1,0) then r else 0
  have hg : Summable g := (geometric_pair_sum hr hr1).1
  have ha : HasSum a r := by simpa only [a] using (hasSum_ite_eq (0,1) r)
  have hb : HasSum b r := by simpa only [b] using (hasSum_ite_eq (1,0) r)
  have hpoint (ij : ℕ×ℕ) : inverseLocalMass z ij ≤ g ij-a ij-b ij := by
    by_cases h01 : ij=(0,1)
    · subst ij
      have hc : inverseCoeff (exponent 0 1)=0 :=
        inverseCoeff_degree_one _ (by simp [degree_exponent])
      simp [inverseLocalMass,hc,g,a,b]
    by_cases h10 : ij=(1,0)
    · subst ij
      have hc : inverseCoeff (exponent 1 0)=0 :=
        inverseCoeff_degree_one _ (by simp [degree_exponent])
      simp [inverseLocalMass,hc,g,a,b]
    · simpa only [g,a,b,if_neg h01,if_neg h10,sub_zero] using
        inverseLocalMass_le_geometric hz ij
  have hsum : (∑' ij, inverseLocalMass z ij) ≤ (∑' ij, (g ij-a ij-b ij)) :=
    (inverseLocalMass_summable hz hz1).tsum_le_tsum hpoint
      ((hg.sub ha.summable).sub hb.summable)
  have hvalue : (∑' ij, (g ij-a ij-b ij)) = ((1-r)⁻¹)^2-2*r := by
    rw [(hg.sub ha.summable).tsum_sub hb.summable,hg.tsum_sub ha.summable,
      ha.tsum_eq,hb.tsum_eq]
    rw [(geometric_pair_sum hr hr1).2]
    ring
  have hden : 0 < 1-r := by linarith
  have hinv0 : 0 ≤ (1-r)⁻¹ := le_of_lt (inv_pos.mpr hden)
  have hinv : (1-r)⁻¹ ≤ 4 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/4)
      (show (1:ℝ)/4 ≤ 1-r by linarith)
    norm_num [one_div] at hh
    exact hh
  have hsquare : ((1-r)⁻¹)^2 ≤ 16 := by nlinarith
  have hcoef : (3-2*r)*((1-r)⁻¹)^2 ≤ 48 := by nlinarith [sq_nonneg ((1-r)⁻¹)]
  have hid : ((1-r)⁻¹)^2-2*r = 1+r^2*((3-2*r)*((1-r)⁻¹)^2) := by
    field_simp [ne_of_gt hden]
    <;> ring
  calc
    (∑' ij, inverseLocalMass z ij) ≤ ((1-r)⁻¹)^2-2*r := hsum.trans_eq hvalue
    _ = 1+r^2*((3-2*r)*((1-r)⁻¹)^2) := hid
    _ ≤ 1+r^2*48 := by nlinarith [mul_le_mul_of_nonneg_left hcoef (sq_nonneg r)]
    _ = 1+432*z^2 := by dsimp [r]; ring

theorem inverseLocalMass_finite (T : Finset (ℕ×ℕ)) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1/4) :
    ∑ ij ∈ T, inverseLocalMass z ij ≤ 1+432*z^2 := by
  exact (Summable.sum_le_tsum T (fun _ _ => inverseLocalMass_nonneg hz _)
    (inverseLocalMass_summable hz hz1)).trans (inverseLocalMass_total hz hz1)

end
end QRH.Record1252270103TwoIdeal

#print axioms QRH.Record1252270103TwoIdeal.inverseLocalMass_summable
#print axioms QRH.Record1252270103TwoIdeal.inverseLocalMass_total
#print axioms QRH.Record1252270103TwoIdeal.inverseLocalMass_finite
