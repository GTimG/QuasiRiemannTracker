/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row105_coefficients : Fin 3 → Fin 4 → ℝ := ![![(109410116524681293557436883/2286144641676056118750000:ℝ),(26112071975074036566664575401/308629526626267576031250000:ℝ),(6627769865407082345731998263/154314763313133788015625000:ℝ),(11836734237570682057141541/2374073281740519815625000:ℝ)],
![(46518063194440873024223509/342921696251408417812500:ℝ),(19263251401006427176906754293/77157381656566894007812500:ℝ),(816035358362424563393108219/5935183204351299539062500:ℝ),(1561733785995679185903942079/77157381656566894007812500:ℝ)],
![(74722811426878895397383507/685843392502816835625000:ℝ),(33855442460922986144372059321/154314763313133788015625000:ℝ),(4361700653416409772176986669/30862952662626757603125000:ℝ),(4432308456595334991924163099/154314763313133788015625000:ℝ)]]
theorem row105_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (11836734237570682057141541/4321868516448519628800000000:ℝ) row105_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row105_coefficients,Fin.sum_univ_succ]
 ring
theorem row105_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row105_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row105_coefficients]
#print axioms row105_identity
#print axioms row105_pos
end
end LewkoStage2Finite
