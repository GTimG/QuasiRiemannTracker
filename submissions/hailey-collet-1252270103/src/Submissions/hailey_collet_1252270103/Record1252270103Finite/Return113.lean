/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row113_coefficients : Fin 3 → Fin 4 → ℝ := ![![(440001509387391283619864642/54011125261962890625:ℝ), (3762004604252682556018378822/162033375785888671875:ℝ), (3569384354080154760262730816/162033375785888671875:ℝ), (225476855597929211020789184/32406675157177734375:ℝ)],
![(2531557257227943118871048807/162033375785888671875:ℝ), (7187557376594123761841118823/162033375785888671875:ℝ), (271657848911546095283541376/6481335031435546875:ℝ), (2135446103422471739118464384/162033375785888671875:ℝ)],
![(9782717559228864754780172923/1296267006287109375000:ℝ), (3074807282738860899364044387/144029667365234375000:ℝ), (3255413926402743095853841184/162033375785888671875:ℝ), (1019095428225132678416812864/162033375785888671875:ℝ)]]
theorem row113_identity (δ p : ℝ) : rowMargin .newSwitch .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (15923366066017698100262701/4832833679589376000000000000:ℝ) row113_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row113_coefficients,Fin.sum_univ_succ]
 ring
theorem row113_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .capC δ p := by
 rw [row113_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row113_coefficients]
#print axioms row113_identity
#print axioms row113_pos
end
end Record1252270103Finite
