/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Fixed-profile rectangular row suprema. The original long factor and the
whole mark product remain outside the two witness variables. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRowwiseMarked

set_option autoImplicit false
namespace QRH.Cycle092.WitnessRowSup
noncomputable section
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open HeckeDetectorRowwisePolynomial

lemma weighted_norm_sq (w : ℝ) (hw : 0 ≤ w) (f p : ℂ) :
    ‖f*((Real.sqrt w:ℂ)*p)‖^2 = w*‖f*p‖^2 := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg w), mul_pow]
  rw [Real.sq_sqrt hw]
  ring

/-- The fixed-point inputs are three moments of the SAME fixed profile and
its actual relative log tests, never a row-dependent profile estimate.
`P` may contain an independent long original ordinary factor and all marks.
Weights are fixed before either witness coordinate, and need not be bounded. -/
theorem weighted_rectangular {Row : Type*} (rows : Finset Row)
    (χ : Row → Character) (W : ℝ → ℂ) (X : ℝ) (hX : 0 < X)
    (cover : Finset (Ideal HeckeFamily.O))
    (hc : ∀ J : Ideal HeckeFamily.O,J ≠ 0 → W ((J.absNorm:ℝ)/X) ≠ 0 → J ∈ cover)
    (weight : Row → ℝ) (hw : ∀ u ∈ rows,0 ≤ weight u) (P : Row → ℂ)
    (a b c d E : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (σ freq : Row → ℝ) (hσ : ∀ u ∈ rows,σ u ∈ Icc a b)
    (hf : ∀ u ∈ rows,freq u ∈ Icc c d)
    (henergy : ∀ n : ℕ,n ≤ 2 → ∀ x ∈ Icc a b,∀ y ∈ Icc c d,
      ∑ u ∈ rows,weight u*‖polynomial (χ u) false ((logProfile^[n]) W) X x y*P u‖^2 ≤ E) :
    ∑ u ∈ rows,weight u*‖polynomial (χ u) false W X (σ u) (freq u)*P u‖^2 ≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  let A : Row → ℂ := fun u => (Real.sqrt (max (weight u) 0):ℂ)*P u
  have he (n : ℕ) (hn : n ≤ 2) (x : ℝ) (hx : x ∈ Icc a b)
      (y : ℝ) (hy : y ∈ Icc c d) :
      ∑ u ∈ rows,‖polynomial (χ u) false ((logProfile^[n]) W) X x y*A u‖^2 ≤ E := by
    convert henergy n hn x hx y hy using 1
    apply Finset.sum_congr rfl
    intro u hu
    simp only [A,max_eq_left (hw u hu)]
    exact weighted_norm_sq _ (hw u hu) _ _
  have h := HeckeDetectorRowwiseMarked.marked_rowwise rows χ false W X hX cover hc A
    a b c d E hab hcd σ freq hσ hf
    (by simpa using he 0 (by norm_num))
    (by simpa using he 1 (by norm_num))
    (by simpa [Function.iterate_succ_apply'] using he 2 (by norm_num))
  convert h using 1
  apply Finset.sum_congr rfl
  intro u hu
  simp only [A,max_eq_left (hw u hu)]
  exact (weighted_norm_sq _ (hw u hu) _ _).symm

/-- The witness real parts lie in [0,1]; the separate frequency interval
cost is linear. Polynomial fixed-point height growth therefore stays polynomial. -/
theorem weighted_height {Row : Type*} (rows : Finset Row)
    (χ : Row → Character) (W : ℝ → ℂ) (X : ℝ) (hX : 0 < X)
    (cover : Finset (Ideal HeckeFamily.O))
    (hc : ∀ J : Ideal HeckeFamily.O,J ≠ 0 → W ((J.absNorm:ℝ)/X) ≠ 0 → J ∈ cover)
    (weight : Row → ℝ) (hw : ∀ u ∈ rows,0 ≤ weight u) (P : Row → ℂ)
    (T E : ℝ) (hT : 0 ≤ T) (hE : 0 ≤ E) (σ freq : Row → ℝ)
    (hσ : ∀ u ∈ rows,σ u ∈ Icc 0 1) (hf : ∀ u ∈ rows,|freq u| ≤ T)
    (henergy : ∀ n : ℕ,n ≤ 2 → ∀ x ∈ Icc (0:ℝ) 1,∀ y ∈ Icc (-T) T,
      ∑ u ∈ rows,weight u*‖polynomial (χ u) false ((logProfile^[n]) W) X x y*P u‖^2 ≤ E) :
    ∑ u ∈ rows,weight u*‖polynomial (χ u) false W X (σ u) (freq u)*P u‖^2 ≤
      12*(1+T)*E := by
  exact (weighted_rectangular rows χ W X hX cover hc weight hw P 0 1 (-T) T E
    (by norm_num) (by linarith) σ freq hσ
    (fun u hu=> by simpa only [mem_Icc,←abs_le] using hf u hu) henergy).trans
    (HeckeDetectorRowwise.source_height_cost hT hE)

#print axioms weighted_rectangular
#print axioms weighted_height
end
end QRH.Cycle092.WitnessRowSup
