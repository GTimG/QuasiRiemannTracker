/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row211_coefficients : Fin 3 → Fin 4 → ℝ := ![![(238927970818692252336461872034893/34501541012648656966019531250:ℝ), (1451709795758415679226080385337871/103504623037945970898058593750:ℝ), (83421373954154490655064926768928/10350462303794597089805859375:ℝ), (48799611216259409242597725790544/51752311518972985449029296875:ℝ)],
![(59257634715222779298898389983348/3450154101264865696601953125:ℝ), (1892837040448801499385825919033036/51752311518972985449029296875:ℝ), (22771885741591371381638420432704/976458707905150668849609375:ℝ), (201095278612951419671294526150496/51752311518972985449029296875:ℝ)],
![(193083962927509237724924895888056/17250770506324328483009765625:ℝ), (1307395222970150814139844874934088/51752311518972985449029296875:ℝ), (924563543475536607816707160925072/51752311518972985449029296875:ℝ), (195415402394678168495350598655152/51752311518972985449029296875:ℝ)]]
theorem row211_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3049975701016213077662357861909/6029581311479846354466816000000000:ℝ) row211_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row211_coefficients,Fin.sum_univ_succ]
 ring
theorem row211_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row211_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row211_coefficients]
#print axioms row211_identity
#print axioms row211_pos
end
end LewkoStage2Return.C30
