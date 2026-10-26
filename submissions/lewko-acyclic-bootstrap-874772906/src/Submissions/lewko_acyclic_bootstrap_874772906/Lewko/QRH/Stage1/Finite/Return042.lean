/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row042_coefficients : Fin 3 → Fin 4 → ℝ := ![![(104336222123457926765993492903/1976341517578125000000:ℝ),(929687460755665896749287878271/5929024552734375000000:ℝ),(920387716059477775797930509879/5929024552734375000000:ℝ),(303708921674185659346623110317/5929024552734375000000:ℝ)],
![(98394304380407861689294524983/988170758789062500000:ℝ),(876207535490555510058800783839/2964512276367187500000:ℝ),(288968900329390278016404309361/988170758789062500000:ℝ),(285882078638838909058295719193/2964512276367187500000:ℝ)],
![(4878997389689492635619736917/104017974609375000000:ℝ),(43419226145543141522196977077/312053923828125000000:ℝ),(8585937267875071931551417139/62410784765625000000:ℝ),(4715817454300232014139773123/104017974609375000000:ℝ)]]
theorem row042_identity (δ p : ℝ) : rowMargin .oldPeak .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (4715817454300232014139773123/49639311015936000000000000000:ℝ) row042_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row042_coefficients,Fin.sum_univ_succ]
 ring
theorem row042_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .capP δ p := by
 rw [row042_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row042_coefficients]
#print axioms row042_identity
#print axioms row042_pos
end
end LewkoStage1Finite
