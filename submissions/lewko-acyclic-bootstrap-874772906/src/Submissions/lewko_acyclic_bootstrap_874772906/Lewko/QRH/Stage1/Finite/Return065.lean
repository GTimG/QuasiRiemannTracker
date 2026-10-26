/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row065_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9617089176155131449067893843409428758656/9332078728609550318939736328125:ℝ),(28564864366652614204880453112679697571968/9332078728609550318939736328125:ℝ),(28279748697092071730563969167815743827968/9332078728609550318939736328125:ℝ),(9331971307963531873041659898545475014656/9332078728609550318939736328125:ℝ)],
![(18610702930093505417387941854857305006496/9332078728609550318939736328125:ℝ),(55263438459883374606350927052988875678112/9332078728609550318939736328125:ℝ),(54697371450625655870253435136248827764736/9332078728609550318939736328125:ℝ),(400991809192047102728565831958161268736/207379527302434451531994140625:ℝ)],
![(1800173060933219257129687418581450400618/1866415745721910063787947265625:ℝ),(26720287914854637150429893029071846162194/9332078728609550318939736328125:ℝ),(2937699516481265191824797847502411991552/1036897636512172257659970703125:ℝ),(8719870728206091494157918597607113764864/9332078728609550318939736328125:ℝ)]]
theorem row065_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2128874689503440306190898095118924259/34792511235308401191937966080000000000:ℝ) row065_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row065_coefficients,Fin.sum_univ_succ]
 ring
theorem row065_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row065_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row065_coefficients]
#print axioms row065_identity
#print axioms row065_pos
end
end LewkoStage1Finite
