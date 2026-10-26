/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row043_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7493203317375748870328355031/37056403454589843750:ℝ),(111240451787741344299441338099/185282017272949218750:ℝ),(55043846284447382730491272208/92641008636474609375:ℝ),(18156628684016082756591490736/92641008636474609375:ℝ)],
![(48469113516063233082087687613/123521344848632812500:ℝ),(431591751214901545661466031159/370564034545898437500:ℝ),(7116353829316589660431594208/6176067242431640625:ℝ),(7039840954614176660534634208/18528201727294921875:ℝ)],
![(564175503276870902067835760203/2964512276367187500000:ℝ),(37200139452594358003140661079/65878050585937500000:ℝ),(51736457513644362449001230704/92641008636474609375:ℝ),(5684748628611920732234847856/30880336212158203125:ℝ)]]
theorem row043_identity (δ p : ℝ) : rowMargin .oldPeak .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (355296789288245045764677991/3684167614464000000000000000:ℝ) row043_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row043_coefficients,Fin.sum_univ_succ]
 ring
theorem row043_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .capC δ p := by
 rw [row043_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row043_coefficients]
#print axioms row043_identity
#print axioms row043_pos
end
end LewkoStage1Finite
