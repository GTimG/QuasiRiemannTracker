/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row194_coefficients : Fin 3 → Fin 4 → ℝ := ![![(30368192561009143828098262802/4793607781307088134765625:ℝ), (73433556215094103420298074142/4793607781307088134765625:ℝ), (6427083544274531035373884642/532623086811898681640625:ℝ), (4926129414795273242055050146/1597869260435696044921875:ℝ)],
![(9818799839281616243505808573/958721556261417626953125:ℝ), (11893721435830063480414763161/532623086811898681640625:ℝ), (71352952833759388108643384828/4793607781307088134765625:ℝ), (13403459107696898002439559244/4793607781307088134765625:ℝ)],
![(128838693444472060569543640661/25565908166971136718750000:ℝ), (790198980001554197963449381087/76697724500913410156250000:ℝ), (1151421085233992686542460088/191744311252283525390625:ℝ), (3555345901591191147635348506/4793607781307088134765625:ℝ)]]
theorem row194_identity (δ p : ℝ) : rowMargin .newKink .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (1777672950795595573817674253/4467966287014987776000000000000:ℝ) row194_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row194_coefficients,Fin.sum_univ_succ]
 ring
theorem row194_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capC δ p := by
 rw [row194_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row194_coefficients]
#print axioms row194_identity
#print axioms row194_pos
end
end Record1252270103Finite
