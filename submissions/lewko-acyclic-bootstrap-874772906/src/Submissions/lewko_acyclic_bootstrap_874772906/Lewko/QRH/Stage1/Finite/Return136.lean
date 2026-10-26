/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row136_coefficients : Fin 3 → Fin 4 → ℝ := ![![(763555353427355972452365808586540250938/19091354420795422256845505859375:ℝ),(437847587265619935402028876468710471902/3818270884159084451369101171875:ℝ),(2089468963317595485507512884522902626516/19091354420795422256845505859375:ℝ),(221260141984821166146322494213630172648/6363784806931807418948501953125:ℝ)],
![(1517339878049176119522815065681291012516/19091354420795422256845505859375:ℝ),(4344653829814431164942347468428309426956/19091354420795422256845505859375:ℝ),(4140681155424183019570485764708494711204/19091354420795422256845505859375:ℝ),(437785001424190497636460766487158765588/6363784806931807418948501953125:ℝ)],
![(761651250606349444812052494831764621378/19091354420795422256845505859375:ℝ),(2178885648025337332504853159187592152166/19091354420795422256845505859375:ℝ),(2074552361303200083656482342767553188638/19091354420795422256845505859375:ℝ),(8764156205573728106809091545489675438/254551392277272296757940078125:ℝ)]]
theorem row136_identity (δ p : ℝ) : rowMargin .newSwitch .P δ p =
 Record12518109.Bernstein.bsum 2 3 (109446250356047624409115191621789691397/48590662443651176829429309505536000000000:ℝ) row136_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row136_coefficients,Fin.sum_univ_succ]
 ring
theorem row136_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .P δ p := by
 rw [row136_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row136_coefficients]
#print axioms row136_identity
#print axioms row136_pos
end
end LewkoStage1Finite
