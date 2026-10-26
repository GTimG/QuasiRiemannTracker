/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row134_coefficients : Fin 3 → Fin 4 → ℝ := ![![(217207759001294581155091630274444765779/5400727842363000016521919921875:ℝ),(624384391724947510863133231420345791737/5400727842363000016521919921875:ℝ),(45968836369211127448677991920578923549/415440603258692308963224609375:ℝ),(2350821890759119379368238195328703459/66675652374851852055826171875:ℝ)],
![(427103190504443387331007310230455886118/5400727842363000016521919921875:ℝ),(245130343235315272248705089821249221578/1080145568472600003304383984375:ℝ),(1170913467486364387107058479281767733906/5400727842363000016521919921875:ℝ),(13791167578473894278994558903925093042/200026957124555556167478515625:ℝ)],
![(212089315863549949120472316615433312699/5400727842363000016521919921875:ℝ),(46754766870263631485748330045187804589/415440603258692308963224609375:ℝ),(579826472323518812684374052833721225659/5400727842363000016521919921875:ℝ),(6818595094851128344944569008767151063/200026957124555556167478515625:ℝ)]]
theorem row134_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (6818595094851128344944569008767151063/3054610628154169999197906927616000000000:ℝ) row134_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row134_coefficients,Fin.sum_univ_succ]
 ring
theorem row134_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row134_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row134_coefficients]
#print axioms row134_identity
#print axioms row134_pos
end
end LewkoStage2Finite
