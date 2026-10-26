/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row002_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13806324343554838147196328437/44440754753150280140625000:ℝ),(2478190658617382172191372833/2962716983543352009375000:ℝ),(66467526965313424064766181661/88881509506300560281250000:ℝ),(438250053750894317195392301/1975144655695568006250000:ℝ)],
![(8429630195665257611661447353/22220377376575140070312500:ℝ),(3556533744476256385058946313/3703396229429190011718750:ℝ),(1188386816002423411892931431/1481358491771676004687500:ℝ),(245151324686633978003837047/1111018868828757003515625:ℝ)],
![(4475040199876486040626566269/44440754753150280140625000:ℝ),(3413208055665592027147285529/14813584917716760046875000:ℝ),(7571212288433238378764280833/44440754753150280140625000:ℝ),(356044274218033299739798103/8888150950630056028125000:ℝ)]]
theorem row002_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (356044274218033299739798103/4045096254864523276800000000:ℝ) row002_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row002_coefficients,Fin.sum_univ_succ]
 ring
theorem row002_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row002_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_coefficients]
#print axioms row002_identity
#print axioms row002_pos
end
end LewkoStage2Finite
