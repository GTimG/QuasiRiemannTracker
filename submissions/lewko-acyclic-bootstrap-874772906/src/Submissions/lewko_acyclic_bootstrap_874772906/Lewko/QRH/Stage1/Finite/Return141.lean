/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row141_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2551374327534456634168011247953736613/745150927756327160252449500000000000:ℝ),(6843632735591061728410134591671015279/745150927756327160252449500000000000:ℝ),(6033142488578753554316235439480820719/745150927756327160252449500000000000:ℝ),(1740884080522148460074112095763542053/745150927756327160252449500000000000:ℝ)],
![(372246512202839165622514999551415061/372575463878163580126224750000000000:ℝ),(947127523456974352808383076973247847/372575463878163580126224750000000000:ℝ),(853265603970229737906986472800252011/372575463878163580126224750000000000:ℝ),(11135383708643782028844735815136769/14903018555126543205048990000000000:ℝ)],
![(1173722407896530338086816751149093509/745150927756327160252449500000000000:ℝ),(312483576173315551371296175450482683/149030185551265432050489900000000000:ℝ),(511646988121928999370241906790750653/745150927756327160252449500000000000:ℝ),(22390199406181752989282033187430747/745150927756327160252449500000000000:ℝ)]]
theorem row141_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (22390199406181752989282033187430747/42390808334582167338806016000000000000:ℝ) row141_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row141_coefficients,Fin.sum_univ_succ]
 ring
theorem row141_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row141_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row141_coefficients]
#print axioms row141_identity
#print axioms row141_pos
end
end LewkoStage1Finite
