/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row055_coefficients : Fin 3 → Fin 4 → ℝ := ![![(27499674429046257912248885708548072/25288200993919306288359375:ℝ), (680893499928030929728812679630089776/210735008282660885736328125:ℝ), (2022970399106643992435438871735263906/632205024847982657208984375:ℝ), (74197957853130705126075816728744042/70245002760886961912109375:ℝ)],
![(798740330064503148405723615753104128/379323014908789594325390625:ℝ), (11863167914491766038570877632357541504/1896615074543947971626953125:ℝ), (3915248867746898555673908885087113696/632205024847982657208984375:ℝ), (143565906718764345933304337098863712/70245002760886961912109375:ℝ)],
![(386543180521540157140562374199656768/379323014908789594325390625:ℝ), (1147917562412541852502283417999687104/379323014908789594325390625:ℝ), (378752578558190599535156166216299968/126441004969596531441796875:ℝ), (13884565400664769140916572401809984/14049000552177392382421875:ℝ)]]
theorem row055_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (216946334385387017826821443778281/3352222106282657881836748800000000:ℝ) row055_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
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
end LewkoStage2Return.C30
