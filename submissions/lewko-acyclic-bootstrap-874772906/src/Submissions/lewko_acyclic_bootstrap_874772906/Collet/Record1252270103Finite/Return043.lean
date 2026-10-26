/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row043_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2397824165130154098236829079732409/11858051627226562500000000:ℝ), (11865644133323786571089760692201887/19763419378710937500000000:ℝ), (366958861594966740449163060192869/617606855584716796875000:ℝ), (363132473087381808157328659392869/1852820566754150390625000:ℝ)],
![(15510114064547055523163816304539507/39526838757421875000000000:ℝ), (138109345001386747812708764483847001/118580516272265625000000000:ℝ), (213490598512557639178102074907723/185282056675415039062500:ℝ), (7822045180606129831730557703249/20586895186157226562500:ℝ)],
![(180536177742484911326703506769088517/948644130178125000000000000:ℝ), (107136415489349438125935442232060929/189728826035625000000000000:ℝ), (1034729322914415554182485249308641/1852820566754150390625000:ℝ), (341084987554528289918864732919547/1852820566754150390625000:ℝ)]]
theorem row043_identity (δ p : ℝ) : rowMargin .oldPeak .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (341084987554528289918864732919547/3536801662029004800000000000000000:ℝ) row043_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
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
end Record1252270103Finite
