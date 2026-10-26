/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row090_coefficients : Fin 3 → Fin 4 → ℝ := ![![(44711343612917479374232450391968930568/1080145568472600003304383984375:ℝ),(644574345474302223657224422178964558608/5400727842363000016521919921875:ℝ),(618907270164006359178526778262921930178/5400727842363000016521919921875:ℝ),(1465837467659931488558847351250385366/40005391424911111233495703125:ℝ)],
![(87082667982045346574807056056482255104/1080145568472600003304383984375:ℝ),(1252942333951689068963035684820401354624/5400727842363000016521919921875:ℝ),(7103683473024198976202516620317163232/31956969481437869920248046875:ℝ),(4728274844403102826754717954266796384/66675652374851852055826171875:ℝ)],
![(42810101241208095789485932996397763008/1080145568472600003304383984375:ℝ),(122982526667837040848029467108595587904/1080145568472600003304383984375:ℝ),(117624622882796470041965599818031630784/1080145568472600003304383984375:ℝ),(1387106076712848648304928359475326144/40005391424911111233495703125:ℝ)]]
theorem row090_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (21673532448638260129764505616801971/9545658212981781247493459148800000000:ℝ) row090_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row090_coefficients,Fin.sum_univ_succ]
 ring
theorem row090_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row090_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row090_coefficients]
#print axioms row090_identity
#print axioms row090_pos
end
end LewkoStage2Finite
