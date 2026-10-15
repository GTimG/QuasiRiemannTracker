import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.PrimeRows.TotalELargeDyad

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open SevenEighths.Parameters SevenEighths.PerturbedCentral
open SevenEighths.PerturbedCanonicalLocalPrep
local notation "O" => HeckeFamily.O

open SevenEighths.PerturbedCanonicalFrontier

lemma large_geometric_scale_totalE (Z ζ δ r : ℝ) (hZ : 0<Z) (n : ℕ) :
    Z^((53/32:ℝ)+(13/16:ℝ)*r+rho0*(3*r/2-3/4))*(Z^(physicalHeight+ζ)*(2:ℝ)^n)^(8/5+δ-r)=
      Z^((53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)-ζ*r+largeRhoCost δ)*((2:ℝ)^(8/5+δ-r))^n := by
  rw [Real.mul_rpow (Real.rpow_nonneg hZ.le _) (by positivity),←Real.rpow_mul hZ.le]
  rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),mul_comm (n:ℝ),
    Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  rw [←mul_assoc,←Real.rpow_add hZ]
  congr 2
  unfold physicalHeight largeRhoCost
  ring

lemma large_geometric_summable_totalE (Z ζ δ r : ℝ) (hZ : 0<Z) (hr : 8/5+δ<r) :
    Summable (fun n : ℕ=>Z^((53/32:ℝ)+(13/16:ℝ)*r+rho0*(3*r/2-3/4))*(Z^(physicalHeight+ζ)*(2:ℝ)^n)^(8/5+δ-r)) := by
  simp_rw [large_geometric_scale_totalE Z ζ δ r hZ]
  exact (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).mul_left _

lemma large_geometric_sum_totalE (Z ζ δ r : ℝ) (hZ : 0<Z) (hr : 8/5+δ<r) :
    (∑'n : ℕ,Z^((53/32:ℝ)+(13/16:ℝ)*r+rho0*(3*r/2-3/4))*(Z^(physicalHeight+ζ)*(2:ℝ)^n)^(8/5+δ-r))=
      Z^((53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)-ζ*r+largeRhoCost δ)*(1-(2:ℝ)^(8/5+δ-r))⁻¹ := by
  simp_rw [large_geometric_scale_totalE Z ζ δ r hZ]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))]

end SevenEighths.ProbeHighRowFamily
end
end OAI
