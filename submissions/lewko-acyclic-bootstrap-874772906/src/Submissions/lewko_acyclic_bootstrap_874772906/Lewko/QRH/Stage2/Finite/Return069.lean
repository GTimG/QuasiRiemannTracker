/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row069_coefficients : Fin 3 → Fin 4 → ℝ := ![![(262683173542278601799009755018601/1666528303243135505273437500:ℝ),(739980010668287971834562017849657/1666528303243135505273437500:ℝ),(173403351120958431864708672099184/416632075810783876318359375:ℝ),(10814789171021287041844160340784/83326415162156775263671875:ℝ)],
![(117446031621429845781756292402586/416632075810783876318359375:ℝ),(328709488768884896256950722501786/416632075810783876318359375:ℝ),(305971119057414580089422755485664/416632075810783876318359375:ℝ),(94696325216833011476192387886464/416632075810783876318359375:ℝ)],
![(17493888851700316594407149113964/138877358603594625439453125:ℝ),(48604983726026588926884282344876/138877358603594625439453125:ℝ),(8976628039892903839355521395712/27775471720718925087890625:ℝ),(13769984108206152657384848747648/138877358603594625439453125:ℝ)]]
theorem row069_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (107578000845360567635819130841/2022548127432261638400000000000:ℝ) row069_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row069_coefficients,Fin.sum_univ_succ]
 ring
theorem row069_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row069_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row069_coefficients]
#print axioms row069_identity
#print axioms row069_pos
end
end LewkoStage2Finite
