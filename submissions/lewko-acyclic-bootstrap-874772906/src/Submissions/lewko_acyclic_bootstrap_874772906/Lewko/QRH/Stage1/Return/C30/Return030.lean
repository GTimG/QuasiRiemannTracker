/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row030_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1438548715243611567729134083267847936/632205024847982657208984375:ℝ), (4272649111678563498555687424430679808/632205024847982657208984375:ℝ), (4229829315873952008269537782093815808/632205024847982657208984375:ℝ), (1395728708196853058377984440930983936/632205024847982657208984375:ℝ)],
![(2773015858800150978276762548653571776/632205024847982657208984375:ℝ), (8233945163513765653722862209858567872/632205024847982657208984375:ℝ), (8149199199248515168544128774035644416/632205024847982657208984375:ℝ), (179217964099233273600985274188709888/42147001656532177147265625:ℝ)],
![(267076199540408870828316215644753228/126441004969596531441796875:ℝ), (3964038248787684837189843051590922364/632205024847982657208984375:ℝ), (1307370884457420613465847582789851136/210735008282660885736328125:ℝ), (1293455180350340645444115150002397184/632205024847982657208984375:ℝ)]]
theorem row030_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (157892478070109942070814837646777/1178515584239996911583232000000000:ℝ) row030_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
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
end LewkoStage1Return.C30
