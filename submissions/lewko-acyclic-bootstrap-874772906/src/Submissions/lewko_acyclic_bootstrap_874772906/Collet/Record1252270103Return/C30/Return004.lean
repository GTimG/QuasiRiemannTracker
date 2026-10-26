/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row004_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1313568243230073340493199479/8888292963191882812500:ℝ), (3768226371626930320711661029/8888292963191882812500:ℝ), (3599296903774649542342908421/8888292963191882812500:ℝ), (1144617651163090655624446871/8888292963191882812500:ℝ)],
![(1074821406670160778517887767/4444146481595941406250:ℝ), (3060174285237705431625363397/4444146481595941406250:ℝ), (2899751759659689789712666493/4444146481595941406250:ℝ), (304790825274589251160063621/1481382160531980468750:ℝ)],
![(172315517333509754088580531/1777658592638376562500:ℝ), (485904026644074152626265393/1777658592638376562500:ℝ), (151895392564686461914948481/592552864212792187500:ℝ), (142091067066400641425910581/1777658592638376562500:ℝ)]]
theorem row004_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (142091067066400641425910581/828448949526390374400000000:ℝ) row004_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
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
end Record1252270103Return.C30
