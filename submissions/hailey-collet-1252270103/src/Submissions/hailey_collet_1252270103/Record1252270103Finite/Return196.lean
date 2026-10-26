/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row196_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11557116325329188281784930720027/19174431125228352539062500:ℝ), (29395400725871100434311346625889/19174431125228352539062500:ℝ), (24278792215014872527906813247597/19174431125228352539062500:ℝ), (47707465292392299076891832161/142032823149839648437500:ℝ)],
![(10625520968251449264264815005139/9587215562614176269531250:ℝ), (26247766160727965151995003665873/9587215562614176269531250:ℝ), (113579119267625999343353519813/52389156079858886718750:ℝ), (1032546726699808398420701093009/1917443112522835253906250:ℝ)],
![(11020723742823688675920770119751/19174431125228352539062500:ℝ), (27048456780859563287688019571257/19174431125228352539062500:ℝ), (5301917674415760332870897372809/4793607781307088134765625:ℝ), (517993765962716671971634003973/1917443112522835253906250:ℝ)]]
theorem row196_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (1032546726699808398420701093009/1830078991161338993049600000000000:ℝ) row196_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row196_coefficients,Fin.sum_univ_succ]
 ring
theorem row196_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newKink .capP δ p := by
 rw [row196_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row196_coefficients]
#print axioms row196_identity
#print axioms row196_pos
end
end Record1252270103Finite
