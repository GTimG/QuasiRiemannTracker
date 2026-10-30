/- Copyright (c) 2026 Joseph Bebel. -/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Nonnegative scalar square-root budgets for the actual two-family swap. -/
namespace Qrh.JointDetector.NaturalSqrtBudget
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem sqrt_product_pull (nL nR KL KR A B D qL qR fL fR EL ER : ℝ)
    (hnL0 : 0 ≤ nL) (hnR0 : 0 ≤ nR) (hKL0 : 0 ≤ KL) (hKR0 : 0 ≤ KR)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hqL : 0 ≤ qL) (hqR : 0 ≤ qR)
    (hfL : 0 ≤ fL) (hfR : 0 ≤ fR) (hEL : 0 ≤ EL) (hER : 0 ≤ ER)
    (hnR : nR ≤ A*qR) (hnL : nL ≤ A*qL) (hKL : KL ≤ B*fL) (hKR : KR ≤ B*fR) :
    Real.sqrt (nR*KL*D*EL)*Real.sqrt (nL*KR*D*ER) ≤
      A*B*D*Real.sqrt (qR*qL)*Real.sqrt (fL*fR)*Real.sqrt EL*Real.sqrt ER := by
  have hL := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hnR hKL hKL0 (mul_nonneg hA hqR)) hD) hEL
  have hR := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hnL hKR hKR0 (mul_nonneg hA hqL)) hD) hER
  calc
    _ ≤ Real.sqrt ((A*qR)*(B*fL)*D*EL)*Real.sqrt ((A*qL)*(B*fR)*D*ER) :=
      mul_le_mul (Real.sqrt_le_sqrt hL) (Real.sqrt_le_sqrt hR)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (((A*qR)*(B*fL)*D*EL)*((A*qL)*(B*fR)*D*ER)) :=
      (Real.sqrt_mul (by positivity) _).symm
    _ = Real.sqrt ((A*B*D)^2*(qR*qL)*(fL*fR)*EL*ER) := by congr 1; ring
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ (A*B*D)^2*(qR*qL)*(fL*fR)*EL),
        Real.sqrt_mul (by positivity : 0 ≤ (A*B*D)^2*(qR*qL)*(fL*fR)),
        Real.sqrt_mul (by positivity : 0 ≤ (A*B*D)^2*(qR*qL)),
        Real.sqrt_mul (sq_nonneg (A*B*D)),Real.sqrt_sq (by positivity : 0 ≤ A*B*D)]

/-- The actual higher-count, pivot-norm and divisor factors pull out with
exactly two copies of the common small-power loss W. -/
theorem sqrt_product_polynomial (nL nR KL KR Ch Cs Zl W Deps qL qR fL fR EL ER : ℝ)
    (hnL0 : 0 ≤ nL) (hnR0 : 0 ≤ nR) (hKL0 : 0 ≤ KL) (hKR0 : 0 ≤ KR)
    (hCh : 0 ≤ Ch) (hCs : 0 ≤ Cs) (hZl : 0 ≤ Zl) (hW : 0 ≤ W) (hDeps : 0 ≤ Deps)
    (hqL : 0 ≤ qL) (hqR : 0 ≤ qR) (hfL : 0 ≤ fL) (hfR : 0 ≤ fR)
    (hEL : 0 ≤ EL) (hER : 0 ≤ ER)
    (hnR : nR ≤ Ch*(16*qR)*W) (hnL : nL ≤ Ch*(16*qL)*W)
    (hKL : KL ≤ Cs*Zl*fL) (hKR : KR ≤ Cs*Zl*fR) :
    Real.sqrt (nR*KL*(Deps*W)*EL)*Real.sqrt (nL*KR*(Deps*W)*ER) ≤
      16*Ch*Cs*Deps*Zl*W^2*Real.sqrt (qR*qL)*Real.sqrt (fL*fR)*Real.sqrt EL*Real.sqrt ER := by
  have hnR' : nR ≤ (16*Ch*W)*qR := hnR.trans_eq (by ring)
  have hnL' : nL ≤ (16*Ch*W)*qL := hnL.trans_eq (by ring)
  have hh := sqrt_product_pull nL nR KL KR (16*Ch*W) (Cs*Zl) (Deps*W) qL qR fL fR EL ER
    hnL0 hnR0 hKL0 hKR0 (by positivity) (mul_nonneg hCs hZl) (mul_nonneg hDeps hW)
    hqL hqR hfL hfR hEL hER hnR' hnL' hKL hKR
  calc
    _ ≤ (16*Ch*W)*(Cs*Zl)*(Deps*W)*Real.sqrt (qR*qL)*Real.sqrt (fL*fR)*Real.sqrt EL*Real.sqrt ER := hh
    _ = _ := by ring

end Qrh.JointDetector.NaturalSqrtBudget

#print axioms Qrh.JointDetector.NaturalSqrtBudget.sqrt_product_pull
#print axioms Qrh.JointDetector.NaturalSqrtBudget.sqrt_product_polynomial
