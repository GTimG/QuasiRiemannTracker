/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row148_coefficients : Fin 3 → Fin 4 → ℝ := ![![(25826423497740608914696060139950721/19177017610959726562500000000:ℝ),(7817746547612704139385982934557759943/2588897377479563085937500000000:ℝ),(164427293043734122696978733753469341/80903043046236346435546875000:ℝ),(29077937561930312200040770763956447/80903043046236346435546875000:ℝ)],
![(1414017938425307194051662332971925347/575310528328791796875000000000:ℝ),(27242961417403783483650898770084266363/5177794754959126171875000000000:ℝ),(26028401512125830722687210396118449/8090304304623634643554687500:ℝ),(3345901556538301445834182625279483/8090304304623634643554687500:ℝ)],
![(5423600495687124211805660331329168519/4602484226630334375000000000000:ℝ),(20231184264238062943968583165834922227/8284471607934601875000000000000:ℝ),(111927676716206750594827462648341683/80903043046236346435546875000:ℝ),(9694245349007147443280640681130561/80903043046236346435546875000:ℝ)]]
theorem row148_identity (δ p : ℝ) : rowMargin .newTop .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (9694245349007147443280640681130561/154433744013540143923200000000000000000:ℝ) row148_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row148_coefficients,Fin.sum_univ_succ]
 ring
theorem row148_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capC δ p := by
 rw [row148_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row148_coefficients]
#print axioms row148_identity
#print axioms row148_pos
end
end LewkoStage1Finite
