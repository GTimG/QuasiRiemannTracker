/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row109_coefficients : Fin 3 → Fin 4 → ℝ := ![![(148246355136412583843294002291/38578690828283447003906250:ℝ),(393485523236506519999635703801/38578690828283447003906250:ℝ),(2052707215943973070723065833/228276277090434597656250:ℝ),(101585005164284642998606424267/38578690828283447003906250:ℝ)],
![(120703905336956505182137130011/19289345414141723501953125:ℝ),(60424180967481671885360877413/3857869082828344700390625:ℝ),(247814491764068891835474779627/19289345414141723501953125:ℝ),(66293309475925950344245022573/19289345414141723501953125:ℝ)],
![(135055945678549745530490527897/38578690828283447003906250:ℝ),(331714759863319273472587498741/38578690828283447003906250:ℝ),(530334298286474061840016539457/77157381656566894007812500:ℝ),(136756212947707287839416347769/77157381656566894007812500:ℝ)]]
theorem row109_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (66293309475925950344245022573/17978973028425841655808000000000:ℝ) row109_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row109_coefficients,Fin.sum_univ_succ]
 ring
theorem row109_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row109_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row109_coefficients]
#print axioms row109_identity
#print axioms row109_pos
end
end LewkoStage2Finite
