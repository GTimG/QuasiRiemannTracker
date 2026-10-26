/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row055_coefficients : Fin 3 → Fin 4 → ℝ := ![![(80728384481197880370315021388077712808/74656629828876402551517890625:ℝ),(29980039805926757912537363744296299136976/9332078728609550318939736328125:ℝ),(29688200760975762793249958298465784563802/9332078728609550318939736328125:ℝ),(1088800769458343474409904570436577725314/1036897636512172257659970703125:ℝ)],
![(1302661905242136563873283815165663928064/622138581907303354595982421875:ℝ),(58037737261311426881192576432052464464256/9332078728609550318939736328125:ℝ),(57458248296587920195400989977545600577632/9332078728609550318939736328125:ℝ),(2106715036286442269330406474775343892704/1036897636512172257659970703125:ℝ)],
![(1891234560975337276730525822148298985152/1866415745721910063787947265625:ℝ),(1871968911494642157832794664620441743552/622138581907303354595982421875:ℝ),(5558368603670922911432389415814680497856/1866415745721910063787947265625:ℝ),(203743998937346921591397916011294916928/207379527302434451531994140625:ℝ)]]
theorem row055_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (3183499983396045649865592437676483077/49482682645771948361867329536000000000:ℝ) row055_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row055_coefficients,Fin.sum_univ_succ]
 ring
theorem row055_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row055_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row055_coefficients]
#print axioms row055_identity
#print axioms row055_pos
end
end LewkoStage1Finite
