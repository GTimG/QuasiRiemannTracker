/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row020_coefficients : Fin 3 → Fin 4 → ℝ := ![![(247192397241282748106557847820719900728/103689548287713744485051953125:ℝ),(3671484027227005617772250464595311603568/518447741438568722425259765625:ℝ),(134638069099754237987508491174172995594/19201768201428471200935546875:ℝ),(2962236190910433361835461208236935262/1280117880095231413395703125:ℝ)],
![(1430866519840755970894367328927105770752/311068644863141233455155859375:ℝ),(21246789858670321943217763884972607536512/1555343224315706167275779296875:ℝ),(2336829086236470541083292262846519081056/172815913812856240808419921875:ℝ),(28555569904488206142024577676055938464/6400589400476157066978515625:ℝ)],
![(689736848966861261851130345675451507904/311068644863141233455155859375:ℝ),(2047810428839376313844167894986309977152/311068644863141233455155859375:ℝ),(225166532166397144000216076457762500288/34563182762571248161683984375:ℝ),(2750720592581310094162757772876559808/1280117880095231413395703125:ℝ)]]
theorem row020_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (42980009259082970221293090201196247/305448023890770460338133401600000000:ℝ) row020_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row020_coefficients,Fin.sum_univ_succ]
 ring
theorem row020_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row020_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row020_coefficients]
#print axioms row020_identity
#print axioms row020_pos
end
end LewkoStage2Finite
