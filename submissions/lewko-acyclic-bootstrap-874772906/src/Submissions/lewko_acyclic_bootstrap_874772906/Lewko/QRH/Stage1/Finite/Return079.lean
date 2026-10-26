/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row079_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6941648356471879176110612/116664026783203125:ℝ),(4044373750715672180338052/23332805356640625:ℝ),(19626902691936032441569814/116664026783203125:ℝ),(2115560764943183571996722/38888008927734375:ℝ)],
![(13388679859348432399586104/116664026783203125:ℝ),(38926458706434884089237832/116664026783203125:ℝ),(37703429505551437946075392/116664026783203125:ℝ),(4055216886154995418807888/38888008927734375:ℝ)],
![(6512117844041569669998092/116664026783203125:ℝ),(18899113292981251479758212/116664026783203125:ℝ),(18270317496485427552329228/116664026783203125:ℝ),(1961107349181915247523036/38888008927734375:ℝ)]]
theorem row079_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (490276837295478811880759/148464645823266816000000000:ℝ) row079_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row079_coefficients,Fin.sum_univ_succ]
 ring
theorem row079_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row079_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row079_coefficients]
#print axioms row079_identity
#print axioms row079_pos
end
end LewkoStage1Finite
