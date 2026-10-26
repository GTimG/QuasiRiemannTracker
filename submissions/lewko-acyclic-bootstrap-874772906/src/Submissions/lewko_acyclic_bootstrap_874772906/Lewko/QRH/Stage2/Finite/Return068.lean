/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row068_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3865702074866113379722473705063089/833264151621567752636718750:ℝ),(3739596772377526653915405452169011/277754717207189250878906250:ℝ),(1807810359012202664719121775461504/138877358603594625439453125:ℝ),(349373603694562217523891339195008/83326415162156775263671875:ℝ)],
![(727124678807947637398620902587558/83326415162156775263671875:ℝ),(43342628931356780729882436122458/1714535291402402783203125:ℝ),(10164184920351176668731451828711168/416632075810783876318359375:ℝ),(1089169935215091441626666194213888/138877358603594625439453125:ℝ)],
![(1708348475627018406136229580705058/416632075810783876318359375:ℝ),(329301110022069492743105451203566/27775471720718925087890625:ℝ),(4757331329517020892498756973248256/416632075810783876318359375:ℝ),(1526142370875598290902005567149824/416632075810783876318359375:ℝ)]]
theorem row068_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5961493636232805823835959246679/97082310116748558643200000000000:ℝ) row068_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row068_coefficients,Fin.sum_univ_succ]
 ring
theorem row068_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row068_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row068_coefficients]
#print axioms row068_identity
#print axioms row068_pos
end
end LewkoStage2Finite
