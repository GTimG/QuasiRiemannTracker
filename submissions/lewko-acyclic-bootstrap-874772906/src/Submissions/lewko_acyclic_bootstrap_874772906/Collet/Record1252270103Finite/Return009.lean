/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row009_coefficients : Fin 3 → Fin 4 → ℝ := ![![(682698335939123570073248514203/197634193787109375000:ℝ), (407340757507600718138795927743/39526838757421875000:ℝ), (1350219638566291431876818660039/131756129191406250000:ℝ), (16575901388902645115913502853/4879856636718750000:ℝ)],
![(220009610139978335871012889171/32939032297851562500:ℝ), (656245440786681616311032891773/32939032297851562500:ℝ), (18124105098311803766156146328/914973119384765625:ℝ), (12012886271806758618977848067/1829946238769531250:ℝ)],
![(637715171230043158684860244573/197634193787109375000:ℝ), (1901839055597705989685848533823/197634193787109375000:ℝ), (630183368487508307853237872159/65878064595703125000:ℝ), (23200971151661558983656493601/7319784955078125000:ℝ)]]
theorem row009_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (23200971151661558983656493601/111780398207336448000000000000:ℝ) row009_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row009_coefficients,Fin.sum_univ_succ]
 ring
theorem row009_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row009_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row009_coefficients]
#print axioms row009_identity
#print axioms row009_pos
end
end Record1252270103Finite
