/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row181_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6476970412986065928721816828366769503/237611365900898756201029687500000:ℝ),(14383058217730420868582658037419298709/237611365900898756201029687500000:ℝ),(9648319222314588348329908886469670159/237611365900898756201029687500000:ℝ),(579674916794472004119585878149463651/79203788633632918733676562500000:ℝ)],
![(40081820443322426902380256957241662463/594028414752246890502574218750000:ℝ),(92073947126392115168337628300353251377/594028414752246890502574218750000:ℝ),(1640227522698655908811181457311427281/14850710368806172262564355468750:ℝ),(2266556259224842067980530285502896221/99004735792041148417095703125000:ℝ)],
![(56700567847206939472352217485719177661/1188056829504493781005148437500000:ℝ),(138452163753030230392878954383483860909/1188056829504493781005148437500000:ℝ),(43465181470224723822105037601692639679/475222731801797512402059375000000:ℝ),(17927971622172182258845654231003985633/792037886336329187336765625000000:ℝ)]]
theorem row181_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (579674916794472004119585878149463651/1181172506599826082049189478400000000000:ℝ) row181_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row181_coefficients,Fin.sum_univ_succ]
 ring
theorem row181_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row181_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row181_coefficients]
#print axioms row181_identity
#print axioms row181_pos
end
end LewkoStage2Finite
