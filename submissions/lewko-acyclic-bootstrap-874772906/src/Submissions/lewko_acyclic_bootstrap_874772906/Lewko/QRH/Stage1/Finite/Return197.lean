/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row197_coefficients : Fin 3 → Fin 4 → ℝ := ![![(24209967453727994457420340784/12782865190192365234375:ℝ),(534721382560882007044468994992/115045786711731287109375:ℝ),(419586623798926627331744477696/115045786711731287109375:ℝ),(20550989664319314080811709952/23009157342346257421875:ℝ)],
![(5001316840321027844653159032/1420318354465818359375:ℝ),(969276399516048697896592301048/115045786711731287109375:ℝ),(146203769170363937438595596288/23009157342346257421875:ℝ),(166849110401774244713291561984/115045786711731287109375:ℝ)],
![(21664195967612026681560542779/12782865190192365234375:ℝ),(457647997713309589178587032211/115045786711731287109375:ℝ),(334337267920257748179924089984/115045786711731287109375:ℝ),(71667033915456399135381942784/115045786711731287109375:ℝ)]]
theorem row197_identity (δ p : ℝ) : rowMargin .newKink .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (139974675616125779561292857/428921780789476786176000000000:ℝ) row197_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row197_coefficients,Fin.sum_univ_succ]
 ring
theorem row197_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capC δ p := by
 rw [row197_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row197_coefficients]
#print axioms row197_identity
#print axioms row197_pos
end
end LewkoStage1Finite
