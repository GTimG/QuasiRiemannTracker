/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row064_coefficients : Fin 3 → Fin 4 → ℝ := ![![(69551164782448489678852122014633989027/66443539002646839075000000000:ℝ),(265623981346808264359484804799918827527/85427407289117364525000000000:ℝ),(1840937157038747149188956942499752799409/597991851023821551675000000000:ℝ),(28929982377643751878734114620572709903/28475802429705788175000000000:ℝ)],
![(605844146140734638723650320696313389307/298995925511910775837500000000:ℝ),(1799149402685956923112439810361440417969/298995925511910775837500000000:ℝ),(356170030485398855273286324003966161357/59799185102382155167500000000:ℝ),(27978321506719042987647891921652560863/14237901214852894087500000000:ℝ)],
![(2930976366455934177020612895696601916527/2989959255119107758375000000000:ℝ),(116022048506219097307726119310984351343/39866123401588103445000000000:ℝ),(8610801665371795785410914294828884534383/2989959255119107758375000000000:ℝ),(27048796710741459114402444687634858097/28475802429705788175000000000:ℝ)]]
theorem row064_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (27048796710741459114402444687634858097/434853831690466485736990310400000000000:ℝ) row064_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row064_coefficients,Fin.sum_univ_succ]
 ring
theorem row064_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row064_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row064_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row064_pos
