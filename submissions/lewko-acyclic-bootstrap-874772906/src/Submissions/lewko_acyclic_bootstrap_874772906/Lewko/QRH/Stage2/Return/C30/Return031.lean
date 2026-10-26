/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row031_coefficients : Fin 3 → Fin 4 → ℝ := ![![(494802287496485456530602181682596664/219292776556693231130859375:ℝ), (4409325769010229154641057000226372904/657878329670079693392578125:ℝ), (4365613286698107836755500340583923532/657878329670079693392578125:ℝ), (133955756228828855397590354291524/61169533209677330859375:ℝ)],
![(2860149692838434650950071749128184304/657878329670079693392578125:ℝ), (2831187356008836808590443205990858032/219292776556693231130859375:ℝ), (1681408339106709228632222378585419616/131575665934015938678515625:ℝ), (308180985071860989978049058231412032/73097592185564410376953125:ℝ)],
![(3967441538932999840362030972241096/1895902967348932833984375:ℝ), (4087115552518655706442878006392643592/657878329670079693392578125:ℝ), (4044308704333008659159394793249121048/657878329670079693392578125:ℝ), (148210570325515200978108781580459752/73097592185564410376953125:ℝ)]]
theorem row031_identity (δ p : ℝ) : rowMargin .oldSmall .P δ p =
 Record12518109.Bernstein.bsum 2 3 (18526321290689400122263597697557469/139534119045930802609127424000000000:ℝ) row031_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row031_coefficients,Fin.sum_univ_succ]
 ring
theorem row031_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .P δ p := by
 rw [row031_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row031_coefficients]
#print axioms row031_identity
#print axioms row031_pos
end
end LewkoStage2Return.C30
