/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One absolute Newton coefficient majorant for every moving residual D. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.NewtonWeightedMass
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.RestoredNewtonPositive
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.JointNewton
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily Record1252270103Source Record1252270103Second
open QRH.Record1252270103KernelMass QRH.Record1252270103Low
open QRH.Record1252270103Source.High.CorrectedCentered
local notation "O"=>ActualEisensteinCubic.O

def coefficientCap (P : Finset (Ideal O)) (j : ℕ) : ℝ :=
  2^(j+1)*(j.factorial:ℝ)/(P.card:ℝ)^j

def assignmentWeight (P : Finset (Ideal O)) (S A : Finset (Ideal O)) : ℝ :=
  coefficientCap P S.card/Real.sqrt (pairNorm (newtonDivisorPair S A))

lemma coefficientCap_nonneg (P : Finset (Ideal O)) (j : ℕ) : 0≤coefficientCap P j := by
  unfold coefficientCap
  positivity

lemma assignmentWeight_nonneg (P S A : Finset (Ideal O)) : 0≤assignmentWeight P S A :=
  div_nonneg (coefficientCap_nonneg P S.card) (Real.sqrt_nonneg _)

/-- The weight is independent of D and the row character. Natural character
zeros are retained in the literal scalar on the left. -/
theorem coefficient_majorant (P : Finset (Ideal O)) (D : Ideal O) (depth : ℕ)
    (hP : 0<P.card) (hbudget : 2*((idealDividingPool P D).card+(depth:ℝ)+1)≤P.card)
    (S A : Finset (Ideal O)) (hS : S.card≤depth)
    (ψ : Ideal O→ℂ) (hψ : ∀I,‖ψ I‖≤1) :
    ‖(newtonCoefficient P.card (idealDividingPool P D).card S.card:ℂ)*
        ψ ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)/
        (Real.sqrt (pairNorm (newtonDivisorPair S A)):ℂ)‖≤assignmentWeight P S A := by
  have hP' : (0:ℝ)<P.card := Nat.cast_pos.mpr hP
  have hj : (S.card:ℝ)≤depth := by exact_mod_cast hS
  have hb : 2*((idealDividingPool P D).card+(S.card:ℝ)+1)≤P.card := by linarith
  have hc0 := newtonCoefficient_nonneg (P.card:ℝ) (idealDividingPool P D).card S.card hP'.le
    (by linarith)
  have hc := newtonCoefficient_bound (P.card:ℝ) (idealDividingPool P D).card S.card hP' hb
  unfold assignmentWeight coefficientCap
  rw [norm_div,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg hc0,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right
    ((mul_le_of_le_one_right hc0 (hψ _)).trans hc) (Real.sqrt_nonneg _)

lemma pair_sqrt_ge_one (P S A : Finset (Ideal O)) (hnz : ∀p∈P,p≠0)
    (hSP : S⊆P) (hAS : A⊆S) : 1≤Real.sqrt (pairNorm (newtonDivisorPair S A)) := by
  have h₁ : (∏p∈A,p)≠0:=Finset.prod_ne_zero_iff.mpr (fun p hp=>hnz p (hSP (hAS hp)))
  have h₂ : (∏p∈S\A,p)≠0:=Finset.prod_ne_zero_iff.mpr (fun p hp=>hnz p (hSP (Finset.mem_sdiff.mp hp).1))
  have hb : (1:ℝ)≤pairNorm (newtonDivisorPair S A) :=
    one_le_mul_of_one_le_of_one_le (ideal_norm_one_le h₁) (ideal_norm_one_le h₂)
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hb

lemma level_mass (P : Finset (Ideal O)) (j : ℕ) (hP : 0<P.card) :
    (∑S∈P.powersetCard j,coefficientCap P S.card*2^S.card)≤2^(j+1)*(j.factorial:ℝ)*2^j := by
  have hP' : (0:ℝ)<P.card:=Nat.cast_pos.mpr hP
  have hchoose : (P.card.choose j:ℝ)≤(P.card:ℝ)^j := by exact_mod_cast Nat.choose_le_pow P.card j
  rw [Finset.sum_powersetCard j P (fun k=>coefficientCap P k*2^k),nsmul_eq_mul]
  calc
    _≤(P.card:ℝ)^j*(coefficientCap P j*2^j) :=
      mul_le_mul_of_nonneg_right hchoose (mul_nonneg (coefficientCap_nonneg P j) (by positivity))
    _=_ := by unfold coefficientCap;field_simp

/-- Uniform total assignment mass, with no row or D in the weights. The
actual ideal norm denominator is retained and paid using its lower bound1. -/
theorem assignment_mass (P : Finset (Ideal O)) (depth : ℕ) (hP : 0<P.card)
    (hnz : ∀p∈P,p≠0) :
    (∑S∈P.powerset.filter (fun S=>S.card≤depth),∑A∈S.powerset,assignmentWeight P S A)≤
      newtonMassBound depth := by
  calc
    _≤∑S∈P.powerset.filter (fun S=>S.card≤depth),coefficientCap P S.card*2^S.card := by
      apply Finset.sum_le_sum
      intro S hS
      have hSP:=Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      calc
        _≤∑A∈S.powerset,coefficientCap P S.card := by
          apply Finset.sum_le_sum
          intro A hA
          exact div_le_self (coefficientCap_nonneg P S.card)
            (pair_sqrt_ge_one P S A hnz hSP (Finset.mem_powerset.mp hA))
        _=_ := by rw [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul];push_cast;ring
    _=∑j∈Finset.range (depth+1),∑S∈P.powersetCard j,coefficientCap P S.card*2^S.card :=
      sum_powerset_le_by_card P depth _
    _≤newtonMassBound depth := by
      apply Finset.sum_le_sum
      intro j _
      exact level_mass P j hP
end
end QRH.Record1252270103Source.Admission.JointNewton
#print axioms QRH.Record1252270103Source.Admission.JointNewton.coefficientCap_nonneg
#print axioms QRH.Record1252270103Source.Admission.JointNewton.assignmentWeight_nonneg
#print axioms QRH.Record1252270103Source.Admission.JointNewton.coefficient_majorant
#print axioms QRH.Record1252270103Source.Admission.JointNewton.pair_sqrt_ge_one
#print axioms QRH.Record1252270103Source.Admission.JointNewton.level_mass
#print axioms QRH.Record1252270103Source.Admission.JointNewton.assignment_mass
