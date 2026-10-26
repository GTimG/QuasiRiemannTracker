/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row020_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1423832277618132832506180460274929096/597253038631011220412143125:ℝ),(13217380424895557433056096583470867956624/1866415745721910063787947265625:ℝ),(13086858018964702664779691121081840165458/1866415745721910063787947265625:ℝ),(479883651016810251593649139691125070426/207379527302434451531994140625:ℝ)],
![(1717044737939761326739916228813489723648/373283149144382012757589453125:ℝ),(25496221094674466306467661051419326026624/1866415745721910063787947265625:ℝ),(25237826948648823040917945885609838844128/1866415745721910063787947265625:ℝ),(925203145314222010942562608695329048416/207379527302434451531994140625:ℝ)],
![(827686590835833796051172657711493711808/373283149144382012757589453125:ℝ),(2457379586258262081058465273473979106624/373283149144382012757589453125:ℝ),(2431805574545316153043784595458527397824/373283149144382012757589453125:ℝ),(89123605818837509329789108855115778112/41475905460486890306398828125:ℝ)]]
theorem row020_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1392556340919336083277954825861184033/9896536529154389672373465907200000000:ℝ) row020_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
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
end LewkoStage1Finite
