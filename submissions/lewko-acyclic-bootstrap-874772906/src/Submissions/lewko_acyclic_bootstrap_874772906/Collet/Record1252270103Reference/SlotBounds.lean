/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uses OpenAI/math's original annular weight and smooth compact support bound. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeSlot
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Reference
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical ContDiff
open HeckeFamily HeckeDyadic HeckePrimeAnnular CenteredMomentPrimeSlot
open CenteredMomentSourceMass
local notation "O"=>HeckeFamily.O

lemma actual_marked_coefficient_bound (W : ℝ→ℂ)
    (hs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W) :
    ∃D : ℝ,0≤D ∧ ∀(χ : Character)(P freq : ℝ),0<P →
      ∀I : Ideal O,Prime I →
      ‖idealCoeff χ I*annularWeight W P (33/50) freq I‖≤D := by
  obtain ⟨D,hD,hbound,_,_⟩ := smooth_annular_bound W 1 2 (by norm_num) hs hW
  refine ⟨D,hD,?_⟩
  intro χ P freq hP I hI
  have hnorm : 0<(I.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.ne_zero)
  let x : ℝ := (I.absNorm:ℝ)/P
  have hx : 0<x := div_pos hnorm hP
  by_cases hw : W x=0
  · simp only [annularWeight,show (I.absNorm:ℝ)/P=x from rfl,hw,zero_mul,mul_zero,norm_zero]
    exact hD
  · have hx1 : 1≤x := (hs hw).1
    have he : (-HeckeDyadic.shift (33/50) freq).re = -(33/50:ℝ) := by
      norm_num [HeckeDyadic.shift]
    have hp : ‖(x:ℂ)^(-HeckeDyadic.shift (33/50) freq)‖≤1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx,he]
      exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    have ha : ‖annularWeight W P (33/50) freq I‖≤D := by
      unfold annularWeight
      change ‖W x*(x:ℂ)^(-HeckeDyadic.shift (33/50) freq)‖≤D
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hp).trans (hbound x)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)).trans ha

lemma actual_marked_support (W : ℝ→ℂ) (hs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (χ : Character) (P freq : ℝ) (hP : 0<P) (I : Ideal O)
    (h : idealCoeff χ I*annularWeight W P (33/50) freq I≠0) :
    (I.absNorm:ℝ)≤2*P := by
  have hw : W ((I.absNorm:ℝ)/P)≠0 := by
    intro hh
    apply h
    simp only [annularWeight,hh,zero_mul,mul_zero]
  exact (div_le_iff₀ hP).mp (hs hw).2

end
end QRH.Record1252270103Reference
#print axioms QRH.Record1252270103Reference.actual_marked_coefficient_bound
#print axioms QRH.Record1252270103Reference.actual_marked_support
