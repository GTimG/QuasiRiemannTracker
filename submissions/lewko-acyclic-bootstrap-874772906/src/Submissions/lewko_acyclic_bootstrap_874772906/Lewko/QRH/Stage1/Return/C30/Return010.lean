/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row010_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1602863807137737916349896581755522396/632205024847982657208984375:ℝ), (4762925131632705664250381124803128156/632205024847982657208984375:ℝ), (4717429610843929592252647848296065024/632205024847982657208984375:ℝ), (1557368105604899801164672680248459264/632205024847982657208984375:ℝ)],
![(3096162921082138176363946868600666896/632205024847982657208984375:ℝ), (9198044031809090709465615013625258768/632205024847982657208984375:ℝ), (9107943179305037236892638367873794048/632205024847982657208984375:ℝ), (1002020565773337105928077574283067392/210735008282660885736328125:ℝ)],
![(59768518770212942700757615987327472/25288200993919306288359375:ℝ), (4437861100625692009868839654985164912/632205024847982657208984375:ℝ), (488139593550657244760326919556161536/70245002760886961912109375:ℝ), (1449608019939509075786880520703475712/632205024847982657208984375:ℝ)]]
theorem row010_identity (δ p : ℝ) : rowMargin .oldSmall .weakC6 δ p =
 Record12518109.Bernstein.bsum 2 3 (44238525999130525994472672140609/294628896059999227895808000000000:ℝ) row010_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row010_coefficients,Fin.sum_univ_succ]
 ring
theorem row010_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .weakC6 δ p := by
 rw [row010_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row010_coefficients]
#print axioms row010_identity
#print axioms row010_pos
end
end LewkoStage1Return.C30
