/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row106_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4623626832202763147172769/1049350051657766390625000:ℝ), (12345365210981380506805777/1049350051657766390625000:ℝ), (10819849925354471572093247/1049350051657766390625000:ℝ), (3098111546575854212460239/1049350051657766390625000:ℝ)],
![(2575616636796163263104261/1049350051657766390625000:ℝ), (12852246177591660062931169/2098700103315532781250000:ℝ), (1349916992260511673104659/262337512914441597656250:ℝ), (24786584272678078784917/16789600826524262250000:ℝ)],
![(537347502806116419607873/262337512914441597656250:ℝ), (1339140493353259119732013/419740020663106556250000:ℝ), (3121827848035417989001903/2098700103315532781250000:ℝ), (220764433053757061102411/1049350051657766390625000:ℝ)]]
theorem row106_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (220764433053757061102411/59696358494308488000000000:ℝ) row106_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row106_coefficients,Fin.sum_univ_succ]
 ring
theorem row106_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row106_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row106_coefficients]
#print axioms row106_identity
#print axioms row106_pos
end
end LewkoStage1Return.C30
