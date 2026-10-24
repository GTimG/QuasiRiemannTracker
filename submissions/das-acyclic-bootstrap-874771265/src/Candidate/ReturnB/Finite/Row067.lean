/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row067_coefficients : Fin 3 → Fin 4 → ℝ := ![![(34909842246791329918036924354035946109/34537789214609515312500000000:ℝ),(311076126717874034720705650364383753079/103613367643828545937500000000:ℝ),(3609116800378977049672989285409714064/1214219152076115772705078125:ℝ),(1190992293129528813348603267218980688/1214219152076115772705078125:ℝ)],
![(16884360381829476403514518616414136697/8634447303652378828125000000:ℝ),(50137946835837265216556330216356121977/8634447303652378828125000000:ℝ),(126882666355678506935147846093723264/22076711855929377685546875:ℝ),(41859281142822319590380312528530688/22076711855929377685546875:ℝ)],
![(742153448311282283221827704211378031/784949754877488984375000000:ℝ),(72705793493705005575103350472255588687/25903341910957136484375000000:ℝ),(1124094471995401723994455899106653664/404739717358705257568359375:ℝ),(41193246603866364474420303922822432/44971079706522806396484375:ℝ)]]
theorem row067_identity (δ p : ℝ) : rowMargin .oldPeak .P δ p =
 Record12518109.Bernstein.bsum 2 3 (1287288956370823889825634497588201/21461035178369414594560000000000000:ℝ) row067_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row067_coefficients,Fin.sum_univ_succ]
 ring
theorem row067_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .P δ p := by
 rw [row067_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row067_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row067_pos
