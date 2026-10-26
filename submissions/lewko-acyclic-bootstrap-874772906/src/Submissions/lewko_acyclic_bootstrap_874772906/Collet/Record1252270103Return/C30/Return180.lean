/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row180_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5570045155417372213672919420651/41401849215178388359223437500:ℝ), (63100924138387556169812920583141/207009246075891941796117187500:ℝ), (46025180765599272024911749812817/207009246075891941796117187500:ℝ), (3554279064646364961292017110977/69003082025297313932039062500:ℝ)],
![(6152088256302197730672599115899/20700924607589194179611718750:ℝ), (12544344836046128890116324312877/20700924607589194179611718750:ℝ), (7609959925547844057337796680247/20700924607589194179611718750:ℝ), (394736594232022762005952994423/6900308202529731393203906250:ℝ)],
![(13653424537265189874873487073447/41401849215178388359223437500:ℝ), (158384942259496899662336046267029/207009246075891941796117187500:ℝ), (29760004925064492933764910640882/51752311518972985449029296875:ℝ), (4778499733963031143003239652289/34501541012648656966019531250:ℝ)]]
theorem row180_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (394736594232022762005952994423/200986043715994878482227200000000:ℝ) row180_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row180_coefficients,Fin.sum_univ_succ]
 ring
theorem row180_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row180_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row180_coefficients]
#print axioms row180_identity
#print axioms row180_pos
end
end Record1252270103Return.C30
