/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row187_coefficients : Fin 3 → Fin 4 → ℝ := ![![(149543341047837617923073094097854661553/1865040617588913826875000000000000:ℝ),(58409359957665657886770005273216585677/373008123517782765375000000000000:ℝ),(2279158624987429444423497411602859121/29141259649826778544921875000000:ℝ),(25403915720658736782812305232898179/14570629824913389272460937500000:ℝ)],
![(8095842642869964192913257825791891069/42387286763384405156250000000000:ℝ),(184294736897412132522562353834476361103/466260154397228456718750000000000:ℝ),(417388180282114254455848225323333137/1821328728114173659057617187500:ℝ),(180511994302743851695235855299241777/7285314912456694636230468750000:ℝ)],
![(54960535091579616960369294120934578737/466260154397228456718750000000000:ℝ),(120954819227583535141060140728159513537/466260154397228456718750000000000:ℝ),(2495526210841090037730801618641354813/14570629824913389272460937500000:ℝ),(432253156589428489601264946211083413/14570629824913389272460937500000:ℝ)]]
theorem row187_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (25403915720658736782812305232898179/869171924723961291079680000000000000000:ℝ) row187_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row187_coefficients,Fin.sum_univ_succ]
 ring
theorem row187_pos {δ p : ℝ} (hd : δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row187_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row187_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row187_pos
