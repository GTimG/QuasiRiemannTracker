/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row072_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4311771968190625262418900473/308629526626267576031250000:ℝ),(1859804454674905811032896511/61725905325253515206250000:ℝ),(3217349981932829713617927161/154314763313133788015625000:ℝ),(17572206795066509198315903/3857869082828344700390625:ℝ)],
![(6364922241013670498774508737/154314763313133788015625000:ℝ),(12571731435938196556639464137/154314763313133788015625000:ℝ),(1502525264610115957533165587/30862952662626757603125000:ℝ),(244494179594636786510174507/30862952662626757603125000:ℝ)],
![(18294217365877278168130117001/308629526626267576031250000:ℝ),(41555831032225150631084765123/308629526626267576031250000:ℝ),(30996845376925351023966520207/308629526626267576031250000:ℝ),(1513707850054347793302374417/61725905325253515206250000:ℝ)]]
theorem row072_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (244494179594636786510174507/28092145356915377587200000000:ℝ) row072_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row072_coefficients,Fin.sum_univ_succ]
 ring
theorem row072_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row072_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row072_coefficients]
#print axioms row072_identity
#print axioms row072_pos
end
end LewkoStage2Finite
