/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row063_coefficients : Fin 3 → Fin 4 → ℝ := ![![(596395180682316292640655894334801/16858800662612870858906250:ℝ), (1756069863169257443817082000800883/16858800662612870858906250:ℝ), (15509221669015923270239206129801067/151729205963515837730156250:ℝ), (5072140730071319265751371171606329/151729205963515837730156250:ℝ)],
![(4669309460731427074443834883130819/70245002760886961912109375:ℝ), (123620753915281325617270892986669297/632205024847982657208984375:ℝ), (363577790148439799974051270357574443/1896615074543947971626953125:ℝ), (23757330586517669195969426648419733/379323014908789594325390625:ℝ)],
![(13147809958017854753549757961033889/421470016565321771472656250:ℝ), (115911422863567556844653375172424769/1264410049695965314417968750:ℝ), (113515489217697697800377032051825187/1264410049695965314417968750:ℝ), (274425299331622980466975413055571/9366000368118261588281250:ℝ)]]
theorem row063_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (274425299331622980466975413055571/4469629475043543842448998400000000:ℝ) row063_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row063_coefficients,Fin.sum_univ_succ]
 ring
theorem row063_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row063_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row063_coefficients]
#print axioms row063_identity
#print axioms row063_pos
end
end LewkoStage1Return.C30
