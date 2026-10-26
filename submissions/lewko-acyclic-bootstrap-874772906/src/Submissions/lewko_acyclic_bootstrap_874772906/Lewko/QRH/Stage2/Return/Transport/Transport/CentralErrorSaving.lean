/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.TransportGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralErrorSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralRectangle
namespace OAI

noncomputable section
variable [QRH.LewkoStage2Return.Geometry.Parameters] [QRH.LewkoStage2Return.Geometry.Bounds]
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.LewkoStage2Return.TransportHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma central_source_crude_scale {Z a e : ℝ} (hZ : 1≤Z) (ha : 0≤a) (he : 0≤e) :
    (Z^(LewkoStage2Return.Transport.Arithmetic.x:ℝ))^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^(LewkoStage2Return.Transport.Arithmetic.y:ℝ))^((1-a-6*e)-1)≤Z^(2:ℝ) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith [LewkoStage2Return.Transport.Arithmetic.x_add_y, LewkoStage2Return.Transport.Transport.ly_coarse, LewkoStage2Return.Transport.Arithmetic.ell_pos, mul_nonneg (by linarith [LewkoStage2Return.Transport.Transport.ly_coarse] : 0 ≤ LewkoStage2Return.Transport.Arithmetic.y) ha, mul_nonneg (by linarith [LewkoStage2Return.Transport.Transport.ly_coarse] : 0 ≤ LewkoStage2Return.Transport.Arithmetic.y) he])

lemma central_prime_product_bound {K : ℕ} (P : Fin K→ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0 < Z) (_hb : 0≤b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=(LewkoStage2Return.Transport.Arithmetic.ell:ℝ)) (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤b^K*Z^(LewkoStage2Return.Transport.Arithmetic.ell:ℝ) := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma central_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→ProbePhysical.PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤Z) (hb : 0≤b) (hζ : ζ≤1/10000000000)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((LewkoStage2Return.Transport.Arithmetic.h:ℝ)+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=(LewkoStage2Return.Transport.Arithmetic.ell:ℝ))
    (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*LewkoStage2Return.Transport.Arithmetic.ell) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (LewkoStage2Return.Transport.Arithmetic.h:ℝ)+ζ≤1 by linarith [LewkoStage2Return.Transport.Transport.h_interval]))
  have hp := central_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=>Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^(LewkoStage2Return.Transport.Arithmetic.ell:ℝ))^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^((LewkoStage2Return.Transport.Arithmetic.ell:ℝ)*(3:ℕ))=Z^(6+3*LewkoStage2Return.Transport.Arithmetic.ell) := by rw [←Real.rpow_add hZ0];congr 1;ring
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring

end SevenEighths.LewkoStage2Return.TransportHighRowFamily

end

end OAI

#print axioms OAI.SevenEighths.LewkoStage2Return.TransportHighRowFamily.central_source_crude_scale
#print axioms OAI.SevenEighths.LewkoStage2Return.TransportHighRowFamily.central_prime_product_bound
#print axioms OAI.SevenEighths.LewkoStage2Return.TransportHighRowFamily.central_arithmetic_cost_bound
