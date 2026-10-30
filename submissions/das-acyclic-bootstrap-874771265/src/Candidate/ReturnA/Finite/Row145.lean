/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row145_coefficients : Fin 3 → Fin 4 → ℝ := ![![(19510374296655030032246279677/3455908639171875000000000:ℝ),(3448739186819862145152548313017/259193147937890625000000000:ℝ),(2620271471958263911742172149863/259193147937890625000000000:ℝ),(634810357387529019008094812621/259193147937890625000000000:ℝ)],
![(1553368071890324599387658723053/172795431958593750000000000:ℝ),(9685154710281381776315368733231/518386295875781250000000000:ℝ),(1470558517399478960825911793527/129596573968945312500000000:ℝ),(214295893746876966287813652509/129596573968945312500000000:ℝ)],
![(12372427259492903901501387339071/2764726911337500000000000000:ℝ),(14369557826345642045769048598937/1658836146802500000000000000:ℝ),(1145081187397368620001415798069/259193147937890625000000000:ℝ),(59752832608321791115757017523/259193147937890625000000000:ℝ)]]
theorem row145_identity (δ p : ℝ) : rowMargin .newTop .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (59752832608321791115757017523/483171047630438400000000000000000:ℝ) row145_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row145_coefficients,Fin.sum_univ_succ]
 ring
theorem row145_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capC δ p := by
 rw [row145_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row145_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row145_pos
