/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row145_coefficients : Fin 3 → Fin 4 → ℝ := ![![(390043095060884472150694015245911/69037263399455015625000000000:ℝ),(68955430820187448885900337921704651/5177794754959126171875000000000:ℝ),(52401211641761756758866594896991989/5177794754959126171875000000000:ℝ),(12699012951140643284268308118730663/5177794754959126171875000000000:ℝ)],
![(31060744334154978206599202606383559/3451863169972750781250000000000:ℝ),(193725603228174312252956532857940493/10355589509918252343750000000000:ℝ),(29434580717203841264860989776746181/2588897377479563085937500000000:ℝ),(4298738160776496856571258517048727/2588897377479563085937500000000:ℝ)],
![(247400608177837735467143583604476013/55229810719564012500000000000000:ℝ),(287458806643786722892584989079280411/33137886431738407500000000000000:ℝ),(22933262237386183365775487688376907/5177794754959126171875000000000:ℝ),(1211630715966795613853794107658969/5177794754959126171875000000000:ℝ)]]
theorem row145_identity (δ p : ℝ) : rowMargin .newTop .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (1211630715966795613853794107658969/9652109000846258995200000000000000000:ℝ) row145_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row145_coefficients,Fin.sum_univ_succ]
 ring
theorem row145_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capC δ p := by
 rw [row145_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row145_coefficients]
#print axioms row145_identity
#print axioms row145_pos
end
end LewkoStage1Finite
