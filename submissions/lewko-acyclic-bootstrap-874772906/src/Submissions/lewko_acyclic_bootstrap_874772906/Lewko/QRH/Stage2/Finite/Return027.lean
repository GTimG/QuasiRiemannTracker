/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row027_coefficients : Fin 3 → Fin 4 → ℝ := ![![(67456051340446169593830636945677/22220377376575140070312500:ℝ),(196483723859952595795271515397831/22220377376575140070312500:ℝ),(63559932484338143610310231497877/7406792458858380023437500:ℝ),(761133269711484195759249272117/274325646624384445312500:ℝ)],
![(19766136682623716383074130978687/3703396229429190011718750:ℝ),(57400727134969738740391649262349/3703396229429190011718750:ℝ),(18510222104041829845732104707699/1234465409809730003906250:ℝ),(1193063655194951961985482222629/246893081961946000781250:ℝ)],
![(51667325305735135650659486528389/22220377376575140070312500:ℝ),(29901581416366292400245119216331/4444075475315028014062500:ℝ),(48032911499317668633730714572743/7406792458858380023437500:ℝ),(5139750368526062219478597546107/2468930819619460007812500:ℝ)]]
theorem row027_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5139750368526062219478597546107/36819365022055749648384000000000:ℝ) row027_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row027_coefficients,Fin.sum_univ_succ]
 ring
theorem row027_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row027_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row027_coefficients]
#print axioms row027_identity
#print axioms row027_pos
end
end LewkoStage2Finite
