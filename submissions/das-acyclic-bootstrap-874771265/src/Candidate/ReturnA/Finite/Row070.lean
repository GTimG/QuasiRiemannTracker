/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row070_coefficients : Fin 3 → Fin 4 → ℝ := ![![(27592558561327442058212135071/106656880220722920937500000:ℝ),(34096766473602789985913463337/53328440110361460468750000:ℝ),(11138032889331148365740014217/21331376044144584187500000:ℝ),(2498374079631593369389213247/17776146703453820156250000:ℝ)],
![(582959069988748152193157141/1481345558621151679687500:ℝ),(40492821893401893777105116/44440366758634550390625:ℝ),(9172142047979393998536869693/13332110027590365117187500:ℝ),(1118972624430772334446874581/6666055013795182558593750:ℝ)],
![(544906438462648022155272433/3333027506897591279296875:ℝ),(2364903944052863786247112711/6666055013795182558593750:ℝ),(273344664621266554542869479/1111009168965863759765625:ℝ),(353982966934693396570649029/6666055013795182558593750:ℝ)]]
theorem row070_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (353982966934693396570649029/12135182816224474560000000000:ℝ) row070_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row070_coefficients,Fin.sum_univ_succ]
 ring
theorem row070_pos {δ p : ℝ} (hd : δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row070_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row070_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row070_pos
