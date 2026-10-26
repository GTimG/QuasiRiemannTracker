/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row042_coefficients : Fin 3 → Fin 4 → ℝ := ![![(50089711374842264073323024909/948651496875000000000:ℝ), (16530501478920752378300055119/105405721875000000000:ℝ), (49095367155232015051057420693/316217165625000000000:ℝ), (48601299530251537821794790917/948651496875000000000:ℝ)],
![(47235453332531802417820953149/474325748437500000000:ℝ), (46737112820833812171825888013/158108582812500000000:ℝ), (138722778078530147953931167483/474325748437500000000:ℝ), (15248964316186837952091485531/158108582812500000000:ℝ)],
![(44500571576048077964873158469/948651496875000000000:ℝ), (44002130886801575426315762621/316217165625000000000:ℝ), (26103558556387685258070949441/189730299375000000000:ℝ), (43011971697581777976280617811/948651496875000000000:ℝ)]]
theorem row042_identity (δ p : ℝ) : rowMargin .oldPeak .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (43011971697581777976280617811/452714128264396800000000000000:ℝ) row042_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row042_coefficients,Fin.sum_univ_succ]
 ring
theorem row042_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .capP δ p := by
 rw [row042_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row042_coefficients]
#print axioms row042_identity
#print axioms row042_pos
end
end Record1252270103Return.C30
