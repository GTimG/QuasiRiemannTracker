/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row125_coefficients : Fin 3 → Fin 4 → ℝ := ![![(486459977903506471237729416287755288/11752008087580502020611429375:ℝ),(43397132942539002260036732094168002672/363614111620683849647630859375:ℝ),(4208573954426924721559130159092838046374/36725025273689068814410716796875:ℝ),(149515575862530133554930665247900561278/4080558363743229868267857421875:ℝ)],
![(592162882603611447632570792375873970944/7345005054737813762882143359375:ℝ),(8520018215242610621043447945418864479872/36725025273689068814410716796875:ℝ),(8163562642670365717130322830994317332384/36725025273689068814410716796875:ℝ),(289370748558669287527702371939424745248/4080558363743229868267857421875:ℝ)],
![(291109087365582801133394414564869935424/7345005054737813762882143359375:ℝ),(836282299184465142463551468991183719872/7345005054737813762882143359375:ℝ),(799848475697068424992169514433708593472/7345005054737813762882143359375:ℝ),(28296999651219664606315828889710534336/816111672748645973653571484375:ℝ)]]
theorem row125_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (442140619550307259473684826401727099/194731830241071604729120397721600000000:ℝ) row125_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row125_coefficients,Fin.sum_univ_succ]
 ring
theorem row125_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row125_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row125_coefficients]
#print axioms row125_identity
#print axioms row125_pos
end
end LewkoStage1Finite
