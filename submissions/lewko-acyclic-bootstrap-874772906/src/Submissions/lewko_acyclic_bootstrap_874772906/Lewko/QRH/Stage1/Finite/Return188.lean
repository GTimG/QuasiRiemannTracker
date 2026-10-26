/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row188_coefficients : Fin 3 → Fin 4 → ℝ := ![![(99150808933087872180314631663770099897/15523977661590149171926031250000000:ℝ),(582190967296206862655346620408972650859/46571932984770447515778093750000000:ℝ),(3856090042207020282476988550165818329/582149162309630593947226171875000:ℝ),(718380247790360048045185453285448911/1455372905774076484868065429687500:ℝ)],
![(6314740634532860423729221500496363873/388099441539753729298150781250000:ℝ),(198100568326697761441106023600905112511/5821491623096305939472261718750000:ℝ),(15238298700103276123505966391924744689/727686452887038242434032714843750:ℝ),(2289940384799481001053966570339944137/727686452887038242434032714843750:ℝ)],
![(10500693053117360188939285660065576503/970248603849384323245376953125000:ℝ),(70525963089308437969536818013607691369/2910745811548152969736130859375000:ℝ),(24608230451336399843559062471278429643/1455372905774076484868065429687500:ℝ),(5068005616304743065683905025588573713/1455372905774076484868065429687500:ℝ)]]
theorem row188_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (718380247790360048045185453285448911/2713011733413258709683585024000000000000:ℝ) row188_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row188_coefficients,Fin.sum_univ_succ]
 ring
theorem row188_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row188_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row188_coefficients]
#print axioms row188_identity
#print axioms row188_pos
end
end LewkoStage1Finite
