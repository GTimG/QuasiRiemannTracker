/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row071_coefficients : Fin 3 → Fin 4 → ℝ := ![![(18362547672760204558551146573/4197340445777462525625000000:ℝ),(49032876830568832560711693959/4197340445777462525625000000:ℝ),(42978110642857051445769948199/4197340445777462525625000000:ℝ),(12307781485048423443609400813/4197340445777462525625000000:ℝ)],
![(5060565831230330637527360981/2098670222888731262812500000:ℝ),(12629398655380500844442513387/2098670222888731262812500000:ℝ),(10621601776085030076508932331/2098670222888731262812500000:ℝ),(122110758077394394783751197/83946808915549250512500000:ℝ)],
![(8547945772810306819003575389/4197340445777462525625000000:ℝ),(2655484791563269386445822423/839468089155492505125000000:ℝ),(6160976307153351300824864713/4197340445777462525625000000:ℝ),(864716799522469555099327987/4197340445777462525625000000:ℝ)]]
theorem row071_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (864716799522469555099327987/238782034248673423680000000000:ℝ) row071_coefficients (0/1:ℝ) (3/8:ℝ) (0/1:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row071_coefficients,Fin.sum_univ_succ]
 ring
theorem row071_pos {δ p : ℝ} (hd : δ∈Set.Icc (0/1:ℝ) (3/8:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row071_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row071_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row071_pos
