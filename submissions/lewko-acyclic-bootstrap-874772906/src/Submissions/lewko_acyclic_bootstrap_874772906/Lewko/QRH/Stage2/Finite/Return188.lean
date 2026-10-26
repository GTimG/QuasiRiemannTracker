/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row188_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10117387918638207400666254758942527927/1584075772672658374673531250000000:ℝ),(59406951479153278581818594756809079269/4752227318017975124020593750000000:ℝ),(393475888910087811634544650899727849/59402841475224689050257421875000:ℝ),(73302563863980861408569954754780701/148507103688061722625643554687500:ℝ)],
![(644358957630947974783079075684439023/39601894316816459366838281250000:ℝ),(20214261749991156237850495011805854001/594028414752246890502574218750000:ℝ),(1554920765643397179445922878811946799/74253551844030861312821777343750:ℝ),(233665592023405750641878483795319467/74253551844030861312821777343750:ℝ)],
![(1071495847344694633907731638788332273/99004735792041148417095703125000:ℝ),(7196502160714715797081323233619190879/297014207376123445251287109375000:ℝ),(2511034412228042684574310672036710913/148507103688061722625643554687500:ℝ),(517141102419591080395967474737738883/148507103688061722625643554687500:ℝ)]]
theorem row188_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (73302563863980861408569954754780701/276837306234334237980278784000000000000:ℝ) row188_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row188_coefficients,Fin.sum_univ_succ]
 ring
theorem row188_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row188_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row188_coefficients]
#print axioms row188_identity
#print axioms row188_pos
end
end LewkoStage2Finite
