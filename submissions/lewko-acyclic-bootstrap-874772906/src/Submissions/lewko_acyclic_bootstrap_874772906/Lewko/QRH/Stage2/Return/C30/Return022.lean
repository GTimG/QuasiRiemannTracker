/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row022_coefficients : Fin 3 → Fin 4 → ℝ := ![![(36249992708868353598706173875804483828/126441004969596531441796875:ℝ), (540969557638964068403023691286991902412/632205024847982657208984375:ℝ), (538194864223044050983587658647679228204/632205024847982657208984375:ℝ), (178475266832516151709133174239709744932/632205024847982657208984375:ℝ)],
![(359140073462041068762247075374999513608/632205024847982657208984375:ℝ), (1071873810729230931562246493016762601112/632205024847982657208984375:ℝ), (526587010615998047860267771310016568/312200012270608719609375:ℝ), (117868317532224887450284718920340154232/210735008282660885736328125:ℝ)],
![(177897420750863340317467826898681432868/632205024847982657208984375:ℝ), (4247409505022582825683527249187834748/5057640198783861257671875:ℝ), (528165769727030353683354870509640162596/632205024847982657208984375:ℝ), (175136999012312891547267875634842251964/632205024847982657208984375:ℝ)]]
theorem row022_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (43784249753078222886816968908710562991/308940789315009750390074769408000000000:ℝ) row022_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row022_coefficients,Fin.sum_univ_succ]
 ring
theorem row022_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row022_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row022_coefficients]
#print axioms row022_identity
#print axioms row022_pos
end
end LewkoStage2Return.C30
