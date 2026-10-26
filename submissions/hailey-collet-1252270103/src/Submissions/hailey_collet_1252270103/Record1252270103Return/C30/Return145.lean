/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row145_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8039408086999929779594549721233/1404312987404109375000000000:ℝ), (475018012133519238760192942129151/35107824685102734375000000000:ℝ), (40260592604849303672581294249721/3900869409455859375000000000:ℝ), (29437507828374246260967483049721/11702608228367578125000000000:ℝ)],
![(639351542956044759976538363062177/70215649370205468750000000000:ℝ), (444833672560492148907275446981331/23405216456735156250000000000:ℝ), (204415493476656419064795038905681/17553912342551367187500000000:ℝ), (30628124795298497378473044435227/17553912342551367187500000000:ℝ)],
![(1689996749042221192000002539719513/374483463307762500000000000000:ℝ), (1969173363655784678891229531824911/224690077984657500000000000000:ℝ), (158262375708611988616441886673407/35107824685102734375000000000:ℝ), (9016232860103869289687510424469/35107824685102734375000000000:ℝ)]]
theorem row145_identity (δ p : ℝ) : rowMargin .newTop .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (9016232860103869289687510424469/65445728670233395200000000000000000:ℝ) row145_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row145_coefficients,Fin.sum_univ_succ]
 ring
theorem row145_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capC δ p := by
 rw [row145_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row145_coefficients]
#print axioms row145_identity
#print axioms row145_pos
end
end Record1252270103Return.C30
