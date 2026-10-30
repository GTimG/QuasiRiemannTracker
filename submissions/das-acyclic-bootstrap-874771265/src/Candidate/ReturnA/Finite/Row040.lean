/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row040_coefficients : Fin 3 → Fin 4 → ℝ := ![![(122898558660919525960288183/474319888593750000000:ℝ),(2973965084506461009044533267/3952665738281250000000:ℝ),(8630477608896556597899992839/11857997214843750000000:ℝ),(2781046321900161719773597613/11857997214843750000000:ℝ)],
![(11083355987463164299436434727/23715994429687500000000:ℝ),(32065646595528406658636956943/23715994429687500000000:ℝ),(858305720554350390339221759/658777623046875000000:ℝ),(826392944324280974417621759/1976332869140625000000:ℝ)],
![(26586433116665539810419420463/126485303625000000000000:ℝ),(45956922067501443460777819561/75891182175000000000000:ℝ),(6888942995951508893467270457/11857997214843750000000:ℝ),(2200652027591802709947556819/11857997214843750000000:ℝ)]]
theorem row040_identity (δ p : ℝ) : rowMargin .oldPeak .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (2200652027591802709947556819/22104908955648000000000000000:ℝ) row040_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row040_coefficients,Fin.sum_univ_succ]
 ring
theorem row040_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .capC δ p := by
 rw [row040_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row040_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row040_pos
