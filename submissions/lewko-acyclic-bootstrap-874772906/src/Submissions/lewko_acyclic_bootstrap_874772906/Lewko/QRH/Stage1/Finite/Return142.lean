/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row142_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3922125661325680146500125678876313449/372575463878163580126224750000000000:ℝ),(7848878298331013924692438284239206123/372575463878163580126224750000000000:ℝ),(4839358062763351909802229937582676249/372575463878163580126224750000000000:ℝ),(34492990715406728712170778338791343/14903018555126543205048990000000000:ℝ)],
![(7128029244100444836357332685267027241/186287731939081790063112375000000000:ℝ),(13888314387312367767574444394383607947/186287731939081790063112375000000000:ℝ),(8132747848815331496754586226924541371/186287731939081790063112375000000000:ℝ),(254380277971541747585235754061592133/37257546387816358012622475000000000:ℝ)],
![(22256347670976444090253731691657741033/372575463878163580126224750000000000:ℝ),(50834963881532955015814937134481875771/372575463878163580126224750000000000:ℝ),(38229798175790841643908539546891339843/372575463878163580126224750000000000:ℝ),(1890011866748586212624948521813441021/74515092775632716025244950000000000:ℝ)]]
theorem row142_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (34492990715406728712170778338791343/6782529333533146774208962560000000000:ℝ) row142_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row142_coefficients,Fin.sum_univ_succ]
 ring
theorem row142_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row142_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row142_coefficients]
#print axioms row142_identity
#print axioms row142_pos
end
end LewkoStage1Finite
