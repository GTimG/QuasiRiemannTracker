/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row003_coefficients : Fin 3 → Fin 4 → ℝ := ![![(561958026196813613782019238637/88881509506300560281250000:ℝ),(313802752649471556290369235899/17776301901260112056250000:ℝ),(485582944192799173472776300501/29627169835433520093750000:ℝ),(9992006258386839757111154681/1975144655695568006250000:ℝ)],
![(403314835295615451323792491997/44440754753150280140625000:ℝ),(1101646784073891824053651729463/44440754753150280140625000:ℝ),(332940058113953896878880258097/14813584917716760046875000:ℝ),(1335151132057408766173473497/197514465569556800625000:ℝ)],
![(91342785960912053704211703959/29627169835433520093750000:ℝ),(241719348423240935777464666301/29627169835433520093750000:ℝ),(70478304179692669265829439421/9875723278477840031250000:ℝ),(6779859961268328107262261769/3291907759492613343750000:ℝ)]]
theorem row003_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6779859961268328107262261769/47941881539135090688000000000:ℝ) row003_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row003_coefficients,Fin.sum_univ_succ]
 ring
theorem row003_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row003_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row003_coefficients]
#print axioms row003_identity
#print axioms row003_pos
end
end LewkoStage2Finite
