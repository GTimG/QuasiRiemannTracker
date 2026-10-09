import QRH.PrimeRows.OptimizedLargeDyad
import OAI.NumberTheory.DirichletL.PrimeRows.GeometricTail
import QRH.Geometry
import OAI.NumberTheory.DirichletL.PrimeRows.LargeDyad

/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Actual physical tails at optimized scales. -/
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.QRHPhysicalTails
open ProbeHighRowFamily

lemma large_geometric_scale (Z ζ δ r : ℝ) (hZ : 0<Z) (n : ℕ) :
    Z^((1+QRH.lx/2+QRH.ly)+QRH.h*r)*(Z^(QRH.h+ζ)*(2:ℝ)^n)^(8/5+δ-r)=
      Z^((1+QRH.lx/2+QRH.ly)+(QRH.h+ζ)*(8/5+δ)-ζ*r)*((2:ℝ)^(8/5+δ-r))^n := by
  have hQRH : (4/5:ℝ)≤QRH.h := by norm_num [QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  rw [Real.mul_rpow (Real.rpow_nonneg hZ.le _) (by positivity),←Real.rpow_mul hZ.le]
  rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),mul_comm (n:ℝ),
    Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  rw [←mul_assoc,←Real.rpow_add hZ]
  congr 2
  ring

lemma large_geometric_summable (Z ζ δ r : ℝ) (hZ : 0<Z) (hr : 8/5+δ<r) :
    Summable (fun n : ℕ=>Z^((1+QRH.lx/2+QRH.ly)+QRH.h*r)*(Z^(QRH.h+ζ)*(2:ℝ)^n)^(8/5+δ-r)) := by
  have hQRH : (4/5:ℝ)≤QRH.h := by norm_num [QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  simp_rw [large_geometric_scale Z ζ δ r hZ]
  exact (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).mul_left _

lemma large_geometric_sum (Z ζ δ r : ℝ) (hZ : 0<Z) (hr : 8/5+δ<r) :
    (∑'n : ℕ,Z^((1+QRH.lx/2+QRH.ly)+QRH.h*r)*(Z^(QRH.h+ζ)*(2:ℝ)^n)^(8/5+δ-r))=
      Z^((1+QRH.lx/2+QRH.ly)+(QRH.h+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹ := by
  have hQRH : (4/5:ℝ)≤QRH.h := by norm_num [QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  simp_rw [large_geometric_scale Z ζ δ r hZ]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))]

lemma exists_large_tail_line (ζ δ saving : ℝ) (hζ : 0<ζ) :
    ∃r : ℝ,(17/50:ℝ)≤r ∧ 8/5+δ<r ∧
      (1+QRH.lx/2+QRH.ly)+(QRH.h+ζ)*(8/5+δ)-ζ*r≤-saving := by
  have hQRH : (4/5:ℝ)≤QRH.h := by norm_num [QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  obtain ⟨r,hr⟩ := exists_gt (max (17/50:ℝ) (max (8/5+δ)
    (((1+QRH.lx/2+QRH.ly)+(QRH.h+ζ)*(8/5+δ)+saving)/ζ)))
  have h1 := (le_max_left (17/50:ℝ) _).trans_lt hr
  have h2 := (le_trans (le_max_left (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  have h3 := (le_trans (le_max_right (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  refine ⟨r,h1.le,h2,?_⟩
  have hh := (div_lt_iff₀ hζ).mp h3
  nlinarith

end SevenEighths.QRHPhysicalTails
end

end OAI
