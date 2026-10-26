/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row063_coefficients : Fin 3 → Fin 4 → ℝ := ![![(23047432809525645716615512587522225097/646830940508002169658358593750:ℝ),(7541954285416933197852266301104097731/71870104500889129962039843750:ℝ),(199871886337688634440337140473297336241/1940492821524006508975075781250:ℝ),(13076261825687732711427397621210674559/388098564304801301795015156250:ℝ)],
![(2706898864550148008363619255348824718341/40426933781750135603647412109375:ℝ),(126423352053098476545906102605730325649/641697361615081517518212890625:ℝ),(23430187847350727973052956717967165555253/121280801345250406810942236328125:ℝ),(1531371294889407054303830343306121632523/24256160269050081362188447265625:ℝ)],
![(2540937526521872810009903879080066002557/80853867563500271207294824218750:ℝ),(2489588955275308492376807715381821921333/26951289187833423735764941406250:ℝ),(1045167015297766683195473662018519582811/11550552509071467315327832031250:ℝ),(477666943559766096888170617162847463647/16170773512700054241458964843750:ℝ)]]
theorem row063_identity (δ p : ℝ) : rowMargin .oldPeak .P δ p =
 Record12518109.Bernstein.bsum 2 3 (477666943559766096888170617162847463647/7716993709785530402721371258880000000000:ℝ) row063_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row063_coefficients,Fin.sum_univ_succ]
 ring
theorem row063_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .P δ p := by
 rw [row063_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row063_coefficients]
#print axioms row063_identity
#print axioms row063_pos
end
end LewkoStage2Finite
