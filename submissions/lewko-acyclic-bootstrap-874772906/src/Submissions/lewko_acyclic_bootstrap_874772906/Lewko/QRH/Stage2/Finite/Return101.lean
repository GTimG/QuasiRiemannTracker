/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row101_coefficients : Fin 3 → Fin 4 → ℝ := ![![(32082106782784215542674718258101566626/802155942883457123481228515625:ℝ),(49530193281869445780929939848635932362/431930123091092297259123046875:ℝ),(614548767428817786971538389880420851708/5615091600184199864368599609375:ℝ),(9296630996730638735312261144279271304/267385314294485707827076171875:ℝ)],
![(446275664000027810269374895975455272044/5615091600184199864368599609375:ℝ),(1277837197226151113674834192718619132836/5615091600184199864368599609375:ℝ),(1217845379743535270825355475110935710828/5615091600184199864368599609375:ℝ),(18394298022009708875005931707989135716/267385314294485707827076171875:ℝ)],
![(17231896351866430033597876928001553694/431930123091092297259123046875:ℝ),(640847532979386619675849349292689835634/5615091600184199864368599609375:ℝ),(122032269496026258418824623217387256402/1123018320036839972873719921875:ℝ),(9206029966220637717905562112298411638/267385314294485707827076171875:ℝ)]]
theorem row101_identity (δ p : ℝ) : rowMargin .oldSwitch .P δ p =
 Record12518109.Bernstein.bsum 2 3 (4598574505502427218751482926997283929/2041619876134217650234139344896000000000:ℝ) row101_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row101_coefficients,Fin.sum_univ_succ]
 ring
theorem row101_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .P δ p := by
 rw [row101_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row101_coefficients]
#print axioms row101_identity
#print axioms row101_pos
end
end LewkoStage2Finite
