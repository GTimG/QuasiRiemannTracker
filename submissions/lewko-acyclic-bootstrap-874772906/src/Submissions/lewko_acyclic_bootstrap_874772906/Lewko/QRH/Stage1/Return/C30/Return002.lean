/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row002_coefficients : Fin 3 → Fin 4 → ℝ := ![![(690158353993964733880022/2222073240797970703125:ℝ), (7432890655024441370786221/8888292963191882812500:ℝ), (13290547314106463101248881/17776585926383765625000:ℝ), (788678461834311983643323/3555317185276753125000:ℝ)],
![(842680017960581487638791/2222073240797970703125:ℝ), (8532761082487370915824253/8888292963191882812500:ℝ), (3563922191525240034754907/4444146481595941406250:ℝ), (8713432527688704352181/39503524280852812500:ℝ)],
![(223628007672151816258769/2222073240797970703125:ℝ), (1023349838667592151180291/4444146481595941406250:ℝ), (252209625013712754370081/1481382160531980468750:ℝ), (17789452488011143194749/444414648159594140625:ℝ)]]
theorem row002_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (17789452488011143194749/202258044317966400000000:ℝ) row002_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row002_coefficients,Fin.sum_univ_succ]
 ring
theorem row002_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row002_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_coefficients]
#print axioms row002_identity
#print axioms row002_pos
end
end LewkoStage1Return.C30
