/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row038_coefficients : Fin 3 → Fin 4 → ℝ := ![![(18144231439422481000991272252351/6666113212972542021093750000:ℝ),(10119736622360254380878717358713/1333222642594508404218750000:ℝ),(15643919678474941700052475403959/2222037737657514007031250000:ℝ),(1608284341533693546763067963407/740679245885838002343750000:ℝ)],
![(13313201093576616869486601804431/3333056606486271010546875000:ℝ),(36239631601974525639439458748493/3333056606486271010546875000:ℝ),(10917223466079021128470907145131/1111018868828757003515625000:ℝ),(1091235272886107355736512721259/370339622942919001171875000:ℝ)],
![(3336799984086763477870266973037/2222037737657514007031250000:ℝ),(8795057076931627633500306473807/2222037737657514007031250000:ℝ),(2555469776351178109208456447951/740679245885838002343750000:ℝ),(245121224364063996119967204787/246893081961946000781250000:ℝ)]]
theorem row038_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (245121224364063996119967204787/3595641115435131801600000000000:ℝ) row038_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row038_coefficients,Fin.sum_univ_succ]
 ring
theorem row038_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row038_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row038_coefficients]
#print axioms row038_identity
#print axioms row038_pos
end
end LewkoStage2Finite
