/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row011_coefficients : Fin 3 → Fin 4 → ℝ := ![![(507786751323828419577126397554196/5555094344143785017578125:ℝ),(499895165371989904621501381417568/1851698114714595005859375:ℝ),(1476165067050259124124983975635223/5555094344143785017578125:ℝ),(3587155735960819474666534739809/41148846993657666796875:ℝ)],
![(949726782961521373604580191243696/5555094344143785017578125:ℝ),(934200338622436893550246162186064/1851698114714595005859375:ℝ),(918778403281998004991036090129512/1851698114714595005859375:ℝ),(180692069955027383371653557514808/1111018868828757003515625:ℝ)],
![(88601534005866232106736026305832/1111018868828757003515625:ℝ),(29025007965233297701229064646904/123446540980973000390625:ℝ),(256677346754126419783078164540776/1111018868828757003515625:ℝ),(84053743055517415624154484024472/1111018868828757003515625:ℝ)]]
theorem row011_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (10506717881939676953019310503059/66274857039700349367091200000000:ℝ) row011_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row011_coefficients,Fin.sum_univ_succ]
 ring
theorem row011_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row011_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row011_coefficients]
#print axioms row011_identity
#print axioms row011_pos
end
end LewkoStage2Finite
