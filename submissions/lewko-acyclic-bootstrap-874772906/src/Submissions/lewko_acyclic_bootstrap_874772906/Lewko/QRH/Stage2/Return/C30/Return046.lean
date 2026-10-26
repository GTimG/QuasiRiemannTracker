/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row046_coefficients : Fin 3 → Fin 4 → ℝ := ![![(71482808960049866178604295335585732/1896615074543947971626953125:ℝ), (7800802361374645653004165831371472/70245002760886961912109375:ℝ), (206826339030009399858617129850653267/1896615074543947971626953125:ℝ), (4512492333115150882390804849280617/126441004969596531441796875:ℝ)],
![(134471596278526101670699492104802352/1896615074543947971626953125:ℝ), (131954834923111152479388288632137168/632205024847982657208984375:ℝ), (129459532177617986435514976876166984/632205024847982657208984375:ℝ), (5079419164947837179858182273475672/75864602981757918865078125:ℝ)],
![(12635409600726946820705045772400424/379323014908789594325390625:ℝ), (12387040912157040124804403155874024/126441004969596531441796875:ℝ), (36422602519481388948870379774104872/379323014908789594325390625:ℝ), (11896867392331881285412216078883224/379323014908789594325390625:ℝ)]]
theorem row046_identity (δ p : ℝ) : rowMargin .oldPeak .weakC2 δ p =
 Record12518109.Bernstein.bsum 2 3 (1487108424041485160676527009860403/22627499217407940702398054400000000:ℝ) row046_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row046_coefficients,Fin.sum_univ_succ]
 ring
theorem row046_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .weakC2 δ p := by
 rw [row046_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row046_coefficients]
#print axioms row046_identity
#print axioms row046_pos
end
end LewkoStage2Return.C30
