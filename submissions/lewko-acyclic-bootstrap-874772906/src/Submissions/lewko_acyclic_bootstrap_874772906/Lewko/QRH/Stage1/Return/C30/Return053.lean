/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row053_coefficients : Fin 3 → Fin 4 → ℝ := ![![(84818726244687313366309084257803798864/632205024847982657208984375:ℝ), (151917858491229084628617140463094562608/379323014908789594325390625:ℝ), (755818054777963702951540407149123016704/1896615074543947971626953125:ℝ), (83561644845509369536848856702353866752/632205024847982657208984375:ℝ)],
![(504705512530083454306947784054177362832/1896615074543947971626953125:ℝ), (100438119585491192730044239234593104752/126441004969596531441796875:ℝ), (499681036057204269997927887893576562688/632205024847982657208984375:ℝ), (497176813795957240220074546716010479616/1896615074543947971626953125:ℝ)],
![(50052230972526965247158230951881360908/379323014908789594325390625:ℝ), (149403586375345744338120495851070496268/379323014908789594325390625:ℝ), (148652090251268175237614967451183181312/379323014908789594325390625:ℝ), (49300733527590613266685843176994045952/379323014908789594325390625:ℝ)]]
theorem row053_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (752269493524026691691373339492707/11313749608703970351199027200000000:ℝ) row053_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row053_coefficients,Fin.sum_univ_succ]
 ring
theorem row053_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row053_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row053_coefficients]
#print axioms row053_identity
#print axioms row053_pos
end
end LewkoStage1Return.C30
