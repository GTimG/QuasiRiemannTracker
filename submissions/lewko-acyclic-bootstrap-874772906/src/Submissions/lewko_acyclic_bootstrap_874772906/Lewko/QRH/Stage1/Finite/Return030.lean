/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row030_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4224143646100097616757700239400831776384/1866415745721910063787947265625:ℝ),(12545089851116775844575707436350488385152/1866415745721910063787947265625:ℝ),(12418277735314471473254324262723733041152/1866415745721910063787947265625:ℝ),(4097330896531041825094367065774076432384/1866415745721910063787947265625:ℝ)],
![(8142583508067572974713356797504122147104/1866415745721910063787947265625:ℝ),(24175728200633479646819252715940293202208/1866415745721910063787947265625:ℝ),(23924769641728276386921515757295693717504/1866415745721910063787947265625:ℝ),(315664945997621172124584893554380906496/74656629828876402551517890625:ℝ)],
![(156845067005538297746237809421826583354/74656629828876402551517890625:ℝ),(17191580923929299744999422646202971618/2756891795748759326126953125:ℝ),(11514555153808149917628744672243335455232/1866415745721910063787947265625:ℝ),(3796980877595278222923319557559588253696/1866415745721910063787947265625:ℝ)]]
theorem row030_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (926997284569159722393388563857321351/6958502247061680238387593216000000000:ℝ) row030_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row030_coefficients,Fin.sum_univ_succ]
 ring
theorem row030_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row030_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row030_coefficients]
#print axioms row030_identity
#print axioms row030_pos
end
end LewkoStage1Finite
