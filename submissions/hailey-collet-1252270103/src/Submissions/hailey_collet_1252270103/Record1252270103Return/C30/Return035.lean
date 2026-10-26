/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row035_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10030496358255061476212009/17776585926383765625000:ℝ), (25246782632848975949390621/17776585926383765625000:ℝ), (525233024958464396903311/444414648159594140625:ℝ), (1442317495551254147613457/4444146481595941406250:ℝ)],
![(377704563811330404765853/493794053510660156250:ℝ), (161199291888842008556386/88882929631918828125:ℝ), (695071987939685091632941/493794053510660156250:ℝ), (789590605145304582384923/2222073240797970703125:ℝ)],
![(537599213773115222860478/2222073240797970703125:ℝ), (388969013505912578015296/740691080265990234375:ℝ), (808567766167429641114892/2222073240797970703125:ℝ), (57992961915776834976494/740691080265990234375:ℝ)]]
theorem row035_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (28996480957888417488247/674193481059888000000000:ℝ) row035_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row035_coefficients,Fin.sum_univ_succ]
 ring
theorem row035_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row035_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row035_coefficients]
#print axioms row035_identity
#print axioms row035_pos
end
end Record1252270103Return.C30
