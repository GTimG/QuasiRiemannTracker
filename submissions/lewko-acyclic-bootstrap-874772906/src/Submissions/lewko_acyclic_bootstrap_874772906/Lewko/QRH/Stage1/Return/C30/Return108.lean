/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row108_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22071702781701042262810733/104935005165776639062500:ℝ), (270493029374495116687630403/524675025828883195312500:ℝ), (218717309725209845132182711/524675025828883195312500:ℝ), (19433139240536466711201991/174891675276294398437500:ℝ)],
![(20957518775046433587357917/52467502582888319531250:ℝ), (46340130811439198928189691/52467502582888319531250:ℝ), (32340034427524120236510401/52467502582888319531250:ℝ), (2290803143282731002726209/17489167527629439843750:ℝ)],
![(37615577892485528160586001/104935005165776639062500:ℝ), (440353816186562287245522707/524675025828883195312500:ℝ), (83660904338428174098097606/131168756457220798828125:ℝ), (13621682236659055965591287/87445837638147199218750:ℝ)]]
theorem row108_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2290803143282731002726209/509408925818099097600000000:ℝ) row108_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row108_coefficients,Fin.sum_univ_succ]
 ring
theorem row108_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row108_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row108_coefficients]
#print axioms row108_identity
#print axioms row108_pos
end
end LewkoStage1Return.C30
