/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row004_coefficients : Fin 3 → Fin 4 → ℝ := ![![(788350559559966538421473081829/5332890684215304421875000:ℝ),(2261536806115208105468919171119/5332890684215304421875000:ℝ),(2160151666155215349587749833871/5332890684215304421875000:ℝ),(686952744264945375701303744581/5332890684215304421875000:ℝ)],
![(645088529382426846397218648197/2666445342107652210937500:ℝ),(1836663432847262878665747185327/2666445342107652210937500:ℝ),(1740382171722140920438006094263/2666445342107652210937500:ℝ),(548791424088519379620727557133/2666445342107652210937500:ℝ)],
![(103425635027789217624606616921/1066578136843060884375000:ℝ),(291645685567586969196636010963/1066578136843060884375000:ℝ),(273509371700285776070307649913/1066578136843060884375000:ℝ),(85285360118291647361090755871/1066578136843060884375000:ℝ)]]
theorem row004_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (85285360118291647361090755871/497061438408155293286400000000:ℝ) row004_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row004_coefficients,Fin.sum_univ_succ]
 ring
theorem row004_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row004_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row004_coefficients]
#print axioms row004_identity
#print axioms row004_pos
end
end LewkoStage1Finite
