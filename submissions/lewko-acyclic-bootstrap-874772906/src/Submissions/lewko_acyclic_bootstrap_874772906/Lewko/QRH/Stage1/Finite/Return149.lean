/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row149_coefficients : Fin 3 → Fin 4 → ℝ := ![![(74895699315138511237005912831177009151/10355589509918252343750000000000:ℝ),(7175910989999346371484573549129172343/414223580396730093750000000000:ℝ),(269653259895508068022537279413638838833/20711179019836504687500000000000:ℝ),(4043273935054518128154695174635615999/1380745267989100312500000000000:ℝ)],
![(70720619438619089973728631900406997509/5177794754959126171875000000000:ℝ),(33066668785949541773457571099513733359/1035558950991825234375000000000:ℝ),(3726178103376909126485819092591919453/161806086092472692871093750000:ℝ),(820832493897749105132899578859325107/172593158498637539062500000000:ℝ)],
![(72128424469894648942036586152772823961/10355589509918252343750000000000:ℝ),(6717967439634738617206491896521184459/414223580396730093750000000000:ℝ),(120260929235145220277204218944160566169/10355589509918252343750000000000:ℝ),(1629344514278093585938567178926918577/690372633994550156250000000000:ℝ)]]
theorem row149_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (1629344514278093585938567178926918577/10542676924657673825157120000000000000000:ℝ) row149_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row149_coefficients,Fin.sum_univ_succ]
 ring
theorem row149_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row149_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row149_coefficients]
#print axioms row149_identity
#print axioms row149_pos
end
end LewkoStage1Finite
