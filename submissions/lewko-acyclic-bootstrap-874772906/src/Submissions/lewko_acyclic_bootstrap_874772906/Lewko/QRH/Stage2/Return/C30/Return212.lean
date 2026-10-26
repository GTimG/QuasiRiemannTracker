/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row212_coefficients : Fin 3 → Fin 4 → ℝ := ![![(651595481593846214373160071427/15334018227843847540453125000:ℝ), (29571021109361069133842835868249/414018492151783883592234375000:ℝ), (6717155724931307718474781041043/207009246075891941796117187500:ℝ), (476982448458862456519430321183/207009246075891941796117187500:ℝ)],
![(749159676506599665786845329874/5750256835441442827669921875:ℝ), (24636309547691488099483359189383/103504623037945970898058593750:ℝ), (1344566224836316610715956319127/10350462303794597089805859375:ℝ), (1959291246712025873077294939619/103504623037945970898058593750:ℝ)],
![(2499751954474390912921058452793/23001027341765771310679687500:ℝ), (45524038337411670938789465883179/207009246075891941796117187500:ℝ), (29609435070919405049650461759547/207009246075891941796117187500:ℝ), (1227316696467864833760204390301/41401849215178388359223437500:ℝ)]]
theorem row212_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (476982448458862456519430321183/376848831967490397154176000000000:ℝ) row212_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row212_coefficients,Fin.sum_univ_succ]
 ring
theorem row212_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row212_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row212_coefficients]
#print axioms row212_identity
#print axioms row212_pos
end
end LewkoStage2Return.C30
