/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row046_coefficients : Fin 3 → Fin 4 → ℝ := ![![(137087121958261518132835837980196/3333056677634565263671875:ℝ),(404961571353947901577659966967232/3333056677634565263671875:ℝ),(398708081177184322453214256344051/3333056677634565263671875:ℝ),(26166701552992974873014908283903/666611335526913052734375:ℝ)],
![(258021722722032647315902723875056/3333056677634565263671875:ℝ),(761593773326952295319578790462512/3333056677634565263671875:ℝ),(749217389623738083387275581288856/3333056677634565263671875:ℝ),(3275267705751738727407556029352/44440755701794203515625:ℝ)],
![(24258294472326066248709692715272/666611335526913052734375:ℝ),(71540080930870072792886434576216/666611335526913052734375:ℝ),(2604259979210424330592187413208/24689308723219001953125:ℝ),(23033205497249236610440443295672/666611335526913052734375:ℝ)]]
theorem row046_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2879150687156154576305055411959/39764915072652423462912000000000:ℝ) row046_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row046_coefficients,Fin.sum_univ_succ]
 ring
theorem row046_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row046_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row046_coefficients]
#print axioms row046_identity
#print axioms row046_pos
end
end LewkoStage1Finite
