/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row005_coefficients : Fin 3 → Fin 4 → ℝ := ![![(57962501665675849501969969/98817096893554687500:ℝ), (168075779576803957251958199/98817096893554687500:ℝ), (162318470246505350437764041/98817096893554687500:ℝ), (52205192335377242687775811/98817096893554687500:ℝ)],
![(41564340105673739084626837/39526838757421875000:ℝ), (600408273720213631636447681/197634193787109375000:ℝ), (144396736922516160238678633/49408548446777343750:ℝ), (46250093624554926185350259/49408548446777343750:ℝ)],
![(164552605417591465150965803/351349677843750000000:ℝ), (473404274474318335353001067/351349677843750000000:ℝ), (566721079950858466470799/439187097304687500:ℝ), (4516412340748746967956373/10979677432617187500:ℝ)]]
theorem row005_identity (δ p : ℝ) : rowMargin .oldSmall .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (4516412340748746967956373/20467602210816000000000000:ℝ) row005_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row005_coefficients,Fin.sum_univ_succ]
 ring
theorem row005_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capC δ p := by
 rw [row005_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row005_coefficients]
#print axioms row005_identity
#print axioms row005_pos
end
end Record1252270103Finite
