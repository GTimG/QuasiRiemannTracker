/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row007_coefficients : Fin 3 → Fin 4 → ℝ := ![![(186438793056111953249045778661/1581073550296875000000:ℝ), (184516161327047008468075039429/527024516765625000000:ℝ), (182598956828276930340279127597/527024516765625000000:ℝ), (36137435911960343773131608633/316214710059375000000:ℝ)],
![(174888329846645354784156263317/790536775148437500000:ℝ), (57659364107923549693875811831/87837419460937500000:ℝ), (513220450760225673330263451107/790536775148437500000:ℝ), (3759433414123535130434164621/17567483892187500000:ℝ)],
![(163688411044067319832411578973/1581073550296875000000:ℝ), (161792329390501791942558023957/527024516765625000000:ℝ), (479706251168051212400710689373/1581073550296875000000:ℝ), (6320706961624526256217927859/63242942011875000000:ℝ)]]
theorem row007_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (6320706961624526256217927859/30180707515980840960000000000:ℝ) row007_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row007_coefficients,Fin.sum_univ_succ]
 ring
theorem row007_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row007_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row007_coefficients]
#print axioms row007_identity
#print axioms row007_pos
end
end Record1252270103Finite
