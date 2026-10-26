/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row192_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2705271413908302649629728547257201/20695701249213535491852459375000:ℝ),(30442003782545685079586374520172623/103478506246067677459262296875000:ℝ),(21988969321190418199125574273041691/103478506246067677459262296875000:ℝ),(1672504981050902372073524913051691/34492835415355892486420765625000:ℝ)],
![(605756804157374979649246195909717/2069570124921353549185245937500:ℝ),(6145105990798346525227694670404731/10347850624606767745926229687500:ℝ),(38863115697540054800759327187919/108924743416913344693960312500:ℝ),(186310573914923934550164022332053/3449283541535589248642076562500:ℝ)],
![(6807806312673850297587246217839629/20695701249213535491852459375000:ℝ),(78962312787115110889608753241868567/103478506246067677459262296875000:ℝ),(29670248896973973777921606591487067/51739253123033838729631148437500:ℝ),(595485388494859368265389108033488/4311604426919486560802595703125:ℝ)]]
theorem row192_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (186310573914923934550164022332053/100467664968033945332892057600000000:ℝ) row192_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row192_coefficients,Fin.sum_univ_succ]
 ring
theorem row192_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row192_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row192_coefficients]
#print axioms row192_identity
#print axioms row192_pos
end
end LewkoStage1Finite
