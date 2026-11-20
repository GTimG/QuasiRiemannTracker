/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row008_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17789681126178838145659823/39526656855468750:ℝ),(52795523932795076721184111/39526656855468750:ℝ),(26111816345968692826744144/19763328427734375:ℝ),(22957053180428196103952/52702209140625:ℝ)],
![(22952073246194000216740609/26351104570312500:ℝ),(68094086681076957422469121/26351104570312500:ℝ),(2020024946280518533696672/790533137109375:ℝ),(16644113580850745438120416/19763328427734375:ℝ)],
![(266357198277956942582495143/632426509687500000:ℝ),(789958840152568595155243943/632426509687500000:ℝ),(8134094906516534978074832/6587776142578125:ℝ),(8039733410967990791326096/19763328427734375:ℝ)]]
theorem row008_identity (δ p : ℝ) : rowMargin .oldSmall .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (502483338185499424457881/2357856923811840000000000:ℝ) row008_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row008_coefficients,Fin.sum_univ_succ]
 ring
theorem row008_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capC δ p := by
 rw [row008_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row008_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row008_pos
