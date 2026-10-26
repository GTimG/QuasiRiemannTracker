/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row013_coefficients : Fin 3 → Fin 4 → ℝ := ![![(48313368316512508909336256131791618788/632205024847982657208984375:ℝ), (144223660046751765832321063690344528556/632205024847982657208984375:ℝ), (143508599528865345475100032305991675948/632205024847982657208984375:ℝ), (9519661407208387562658114949487753236/126441004969596531441796875:ℝ)],
![(18980588964143909382751091031166908968/126441004969596531441796875:ℝ), (283283057593818988735433056089826586456/632205024847982657208984375:ℝ), (281860058367314516925731770888480855192/632205024847982657208984375:ℝ), (31159981349659589886531231651496271192/210735008282660885736328125:ℝ)],
![(46596887337371077553170819926747264452/632205024847982657208984375:ℝ), (5563253303384928518173203872727628108/25288200993919306288359375:ℝ), (46124465430375843066844010279008339948/210735008282660885736328125:ℝ), (45888950261091212751850013320581581596/632205024847982657208984375:ℝ)]]
theorem row013_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (11472237565272803187962503330145395399/77235197328752437597518692352000000000:ℝ) row013_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row013_coefficients,Fin.sum_univ_succ]
 ring
theorem row013_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row013_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row013_coefficients]
#print axioms row013_identity
#print axioms row013_pos
end
end LewkoStage1Return.C30
