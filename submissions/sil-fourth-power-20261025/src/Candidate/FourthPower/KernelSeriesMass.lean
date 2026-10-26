/- Copyright (c) 2026 Sil. Apache-2.0.
Weighted absolute coefficient mass and its genuine Cauchy-product inequality.
These generic lemmas connect the marked formal inverse to an analytic bound.
-/
import Candidate.FourthPower.KernelInverseMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelSeriesMass
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal
open KernelFormal

def pairExponent : (ℕ × ℕ) ≃ Exponent where
  toFun ij := exponent ij.1 ij.2
  invFun n := (n 0,n 1)
  left_inv ij := by rcases ij with ⟨i,j⟩; simp [exponent]
  right_inv n := exponent_reconstruct n

def weight (A : LocalSeries) (z : ℝ) (n : Exponent) : ℝ :=
  |((MvPowerSeries.coeff n A : ℤ) : ℝ)| * z^(degree n)

theorem weight_nonneg (A : LocalSeries) {z : ℝ} (hz : 0 ≤ z) (n : Exponent) :
    0 ≤ weight A z n := mul_nonneg (abs_nonneg _) (pow_nonneg hz _)

theorem degree_add (n m : Exponent) : degree (n+m) = degree n+degree m := by
  simp only [degree,Finsupp.add_apply]
  omega

theorem weight_mul_le (A B : LocalSeries) {z : ℝ} (hz : 0 ≤ z) (n : Exponent) :
    weight (A*B) z n ≤ ∑ uv ∈ Finset.antidiagonal n, weight A z uv.1*weight B z uv.2 := by
  unfold weight
  rw [MvPowerSeries.coeff_mul]
  push_cast
  calc
    _ ≤ (∑ uv ∈ Finset.antidiagonal n,
        |((MvPowerSeries.coeff uv.1 A : ℤ) : ℝ)*((MvPowerSeries.coeff uv.2 B : ℤ) : ℝ)|)*z^(degree n) :=
      mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg hz _)
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro uv huv
      have he : uv.1+uv.2=n := Finset.mem_antidiagonal.mp huv
      rw [← he,degree_add,pow_add,abs_mul]
      ring

theorem mass_mul (A B : LocalSeries) {z : ℝ} (hz : 0 ≤ z)
    (hA : Summable (weight A z)) (hB : Summable (weight B z)) :
    Summable (weight (A*B) z) ∧
      (∑' n, weight (A*B) z n) ≤ (∑' n, weight A z n)*(∑' n, weight B z n) := by
  have hp := hA.mul_of_nonneg hB (weight_nonneg A hz) (weight_nonneg B hz)
  have hc := summable_sum_mul_antidiagonal_of_summable_mul hp
  have hs := Summable.of_nonneg_of_le (weight_nonneg (A*B) hz) (weight_mul_le A B hz) hc
  refine ⟨hs,?_⟩
  rw [hA.tsum_mul_tsum_eq_tsum_sum_antidiagonal hB hp]
  exact hs.tsum_le_tsum (weight_mul_le A B hz) hc

theorem finite_polynomial_mass {α : Type*} [Fintype α] (c : α → ℤ) (e : α → Exponent)
    {z : ℝ} (hz : 0 ≤ z) :
    Summable (weight (∑ i : α, MvPowerSeries.monomial (e i) (c i)) z) ∧
      (∑' n, weight (∑ i : α, MvPowerSeries.monomial (e i) (c i)) z n) ≤
        ∑ i : α, |(c i : ℝ)| *z^(degree (e i)) := by
  let g : Exponent → ℝ := fun n => ∑ i : α,
    if n=e i then |(c i : ℝ)| *z^(degree (e i)) else 0
  have hi (i : α) : HasSum (fun n : Exponent =>
      if n=e i then |(c i : ℝ)| *z^(degree (e i)) else 0) (|(c i : ℝ)| *z^(degree (e i))) :=
    hasSum_ite_eq (e i) _
  have hg : Summable g := summable_sum (fun i _ => (hi i).summable)
  have htotal : (∑' n, g n) = ∑ i : α, |(c i : ℝ)| *z^(degree (e i)) := by
    rw [Summable.tsum_finsetSum (fun i _ => (hi i).summable)]
    exact Finset.sum_congr rfl (fun i _ => (hi i).tsum_eq)
  have hpoint (n : Exponent) : weight (∑ i : α, MvPowerSeries.monomial (e i) (c i)) z n ≤ g n := by
    unfold weight
    rw [map_sum]
    push_cast
    calc
      _ ≤ (∑ i : α, |((MvPowerSeries.coeff n (MvPowerSeries.monomial (e i) (c i)) : ℤ) : ℝ)|)*
          z^(degree n) := mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg hz _)
      _ = g n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases he : n=e i
        · subst n
          simp
        · simp [MvPowerSeries.coeff_monomial,he]
  have hs := Summable.of_nonneg_of_le (weight_nonneg _ hz) hpoint hg
  exact ⟨hs,(hs.tsum_le_tsum hpoint hg).trans_eq htotal⟩

theorem reciprocal_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 2/5) :
    Summable (weight reciprocalSeries z) := by
  apply pairExponent.summable_iff.mp
  have he : weight reciprocalSeries z ∘ pairExponent = KernelInverseMass.localMass z := by
    funext ij
    simp [pairExponent,weight,degree_exponent,KernelInverseMass.localMass,reciprocalCoeff]
  rw [he]
  exact KernelInverseMass.localMass_summable hz hz1

theorem reciprocal_mass {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 2/5) :
    (∑' n, weight reciprocalSeries z n) ≤ 1+400*z^3 := by
  rw [← pairExponent.tsum_eq (weight reciprocalSeries z)]
  simpa [Function.comp_def,pairExponent,weight,degree_exponent,KernelInverseMass.localMass,reciprocalCoeff]
    using KernelInverseMass.localMass_total hz hz1

end
end Candidate.FourthPower.KernelSeriesMass
