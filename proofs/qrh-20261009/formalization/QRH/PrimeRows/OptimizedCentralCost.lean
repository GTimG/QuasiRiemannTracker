import OAI.NumberTheory.DirichletL.PrimeRows.CentralErrorSaving
import QRH.Geometry
import OAI.NumberTheory.DirichletL.PrimeRows.CentralRectangle

/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Actual cube transport at optimized scales; original row objects unchanged. -/
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.QRHPhysicalTails
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma central_source_crude_scale {Z a e : ℝ} (hZ : 1≤Z) (ha : 0≤a) (he : 0≤e) :
    (Z^QRH.lx)^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^QRH.ly)^((1-a-6*e)-1)≤Z^(2:ℝ) := by
  have hQRH : QRH.h≤9/10 := by norm_num [QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hlx : 0≤QRH.lx ∧ QRH.lx≤1 := by norm_num [QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hly : 0≤QRH.ly := by norm_num [QRH.ly,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)


lemma central_prime_product_bound {K : ℕ} (P : Fin K→PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (_hb : 0≤b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=QRH.ell) (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤b^K*Z^QRH.ell := by
  have hQRH : QRH.h≤9/10 := by norm_num [QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hlx : 0≤QRH.lx ∧ QRH.lx≤1 := by norm_num [QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hly : 0≤QRH.ly := by norm_num [QRH.ly,QRH.M,QRH.b,QRH.ell,QRH.theta]
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]


lemma central_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤Z) (hb : 0≤b) (hζ : ζ≤1/48)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^(QRH.h+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=QRH.ell)
    (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*QRH.ell) := by
  have hQRH : QRH.h≤9/10 := by norm_num [QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hlx : 0≤QRH.lx ∧ QRH.lx≤1 := by norm_num [QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hly : 0≤QRH.ly := by norm_num [QRH.ly,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show QRH.h+ζ≤1 by linarith))
  have hp := central_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=>Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^QRH.ell)^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^(QRH.ell*(3:ℕ))=Z^(6+3*QRH.ell) := by rw [←Real.rpow_add hZ0]; congr 1; norm_num; ring
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring


end SevenEighths.QRHPhysicalTails
end
end OAI
