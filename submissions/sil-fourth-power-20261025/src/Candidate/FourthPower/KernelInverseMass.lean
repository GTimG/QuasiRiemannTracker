/- Copyright (c) 2026 Sil. Apache-2.0.
Central absolute mass for the actual fifth-free reciprocal series.
A 3-by-3 zero-coefficient box gives a summable cubic tail; a sharper fifth-degree
tail is unnecessary for this uniform mass bound.
-/
import Candidate.FourthPower.KernelInverseCoefficients
import Submissions.hailey_collet_1252270103.Record1252270103TwoIdeal.LocalMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelInverseMass
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal
open KernelFormal KernelInverseCoefficients

def localMass (z : ℝ) (ij : ℕ × ℕ) : ℝ :=
  |(reciprocalCoeff (exponent ij.1 ij.2) : ℝ)| * z^(ij.1+ij.2)

theorem localMass_nonneg {z : ℝ} (hz : 0 ≤ z) (ij : ℕ × ℕ) : 0 ≤ localMass z ij :=
  mul_nonneg (abs_nonneg _) (pow_nonneg hz _)

theorem localMass_geometric {z : ℝ} (hz : 0 ≤ z) (ij : ℕ × ℕ) :
    localMass z ij ≤ (2*z)^(ij.1+ij.2) := by
  unfold localMass
  calc
    _ ≤ 2^(ij.1+ij.2)*z^(ij.1+ij.2) :=
      mul_le_mul_of_nonneg_right (by simpa only [degree_exponent] using
        (reciprocalCoeff_abs_bound (exponent ij.1 ij.2))) (pow_nonneg hz _)
    _ = _ := (mul_pow _ _ _).symm

theorem localMass_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 2/5) :
    Summable (localMass z) :=
  Summable.of_nonneg_of_le (localMass_nonneg hz) (localMass_geometric hz)
    (geometric_pair_sum (by positivity : 0 ≤ 2*z) (by linarith : 2*z < 1)).1

/-- The O(z^3) tail suffices for the global Euler product at z=N(P)^(-1/2).
This bound includes all coefficients, not just a fixed finite truncation. -/
theorem localMass_total {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 2/5) :
    (∑' ij : ℕ × ℕ, localMass z ij) ≤ 1+400*z^3 := by
  let r := 2*z
  let box := Finset.range 3 ×ˢ Finset.range 3
  let g : ℕ × ℕ → ℝ := fun ij => r^(ij.1+ij.2)
  let f : ℕ × ℕ → ℝ := fun ij => if ij ∈ box then g ij else 0
  let d : ℕ × ℕ → ℝ := fun ij => if ij=(0,0) then 1 else 0
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrq : r ≤ 4/5 := by dsimp [r]; linarith
  have hr1 : r < 1 := by linarith
  have hg : Summable g := (geometric_pair_sum hr hr1).1
  have hfzero : ∀ ij ∉ box, f ij=0 := by intro ij hij; simp only [f,ite_eq_right hij]
  have hf : Summable f := summable_of_ne_finset_zero hfzero
  have hd : HasSum d (1 : ℝ) := by simpa only [d] using hasSum_ite_eq (0,0) (1 : ℝ)
  have hftotal : (∑' ij, f ij) = (1+r+r^2)^2 := by
    rw [tsum_eq_sum hfzero]
    calc
      _ = ∑ ij ∈ box, g ij := Finset.sum_congr rfl (fun ij hij => by simp [f,hij])
      _ = _ := by norm_num [box,g,Finset.sum_product,Finset.sum_range_succ]; ring
  have hpoint (ij : ℕ × ℕ) : localMass z ij ≤ g ij-f ij+d ij := by
    by_cases hzero : ij=(0,0)
    · subst ij
      norm_num [localMass,g,f,d,box,exponent,reciprocalCoeff_zero]
    by_cases hb : ij ∈ box
    · obtain ⟨hi,hj⟩ := Finset.mem_product.mp hb
      have hi3 := Finset.mem_range.mp hi
      have hj3 := Finset.mem_range.mp hj
      have hn : exponent ij.1 ij.2 ≠ 0 := by
        intro he
        obtain ⟨h0,h1⟩ := (exponent_eq_zero _ _).mp he
        exact hzero (Prod.ext h0 h1)
      have hdeg : degree (exponent ij.1 ij.2) < 5 := by rw [degree_exponent]; omega
      have hc := reciprocalCoeff_small_degree _ hn hdeg
      simp [localMass,hc,f,d,hb,hzero]
    · simpa only [g,r,f,d,ite_eq_right hb,ite_eq_right hzero,sub_zero,add_zero] using
        localMass_geometric hz ij
  have hsum := (localMass_summable hz hz1).tsum_le_tsum hpoint ((hg.sub hf).add hd.summable)
  have htotal : (∑' ij, (g ij-f ij+d ij)) = ((1-r)⁻¹)^2-(1+r+r^2)^2+1 := by
    rw [(hg.sub hf).tsum_add hd.summable,hg.tsum_sub hf,hftotal,hd.tsum_eq,
      (geometric_pair_sum hr hr1).2]
  have hden : 0 < 1-r := by linarith
  have hinv0 : 0 ≤ (1-r)⁻¹ := (inv_pos.mpr hden).le
  have hinv : (1-r)⁻¹ ≤ 5 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/5)
      (show (1:ℝ)/5 ≤ 1-r by linarith)
    norm_num [one_div] at hh
    exact hh
  have hsquare : ((1-r)⁻¹)^2 ≤ 25 := by nlinarith
  have hcoef : (2-r^3)*((1-r)⁻¹)^2 ≤ 50 := by
    nlinarith [sq_nonneg ((1-r)⁻¹),pow_nonneg hr 3,
      mul_nonneg (pow_nonneg hr 3) (sq_nonneg ((1-r)⁻¹))]
  have hid : ((1-r)⁻¹)^2-(1+r+r^2)^2+1 = 1+r^3*((2-r^3)*((1-r)⁻¹)^2) := by
    field_simp [ne_of_gt hden]
    ring
  calc
    _ ≤ ((1-r)⁻¹)^2-(1+r+r^2)^2+1 := hsum.trans_eq htotal
    _ = 1+r^3*((2-r^3)*((1-r)⁻¹)^2) := hid
    _ ≤ 1+r^3*50 := by nlinarith [mul_le_mul_of_nonneg_left hcoef (pow_nonneg hr 3)]
    _ = _ := by dsimp [r]; ring

theorem localMass_finite (T : Finset (ℕ × ℕ)) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 2/5) :
    (∑ ij ∈ T, localMass z ij) ≤ 1+400*z^3 :=
  (Summable.sum_le_tsum T (fun _ _ => localMass_nonneg hz _) (localMass_summable hz hz1)).trans
    (localMass_total hz hz1)

end
end Candidate.FourthPower.KernelInverseMass
