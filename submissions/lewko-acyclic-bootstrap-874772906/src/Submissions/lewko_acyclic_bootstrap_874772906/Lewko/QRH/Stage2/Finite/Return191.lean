/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row191_coefficients : Fin 3 → Fin 4 → ℝ := ![![(695646026404204043875244860589213/64674049343029141450354312500000:ℝ),(280334033529612696393968782565707/12934809868605828290070862500000:ℝ),(874127093595243638817516665298397/64674049343029141450354312500000:ℝ),(6375320245847982656268934522363/2586961973721165658014172500000:ℝ)],
![(1242745514184906969116280193796717/32337024671514570725177156250000:ℝ),(2423390568796556988909555249257987/32337024671514570725177156250000:ℝ),(284131078921301673498195940167443/6467404934302914145035431250000:ℝ),(44514089516897815813063229075189/6467404934302914145035431250000:ℝ)],
![(3859414580942542420768653527004221/64674049343029141450354312500000:ℝ),(8811730874880307846684032298470983/64674049343029141450354312500000:ℝ),(6622761855158534393130689465139007/64674049343029141450354312500000:ℝ),(327113155280006085990106738734449/12934809868605828290070862500000:ℝ)]]
theorem row191_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6375320245847982656268934522363/1177355138262432726136227840000000:ℝ) row191_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row191_coefficients,Fin.sum_univ_succ]
 ring
theorem row191_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row191_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row191_coefficients]
#print axioms row191_identity
#print axioms row191_pos
end
end LewkoStage2Finite
