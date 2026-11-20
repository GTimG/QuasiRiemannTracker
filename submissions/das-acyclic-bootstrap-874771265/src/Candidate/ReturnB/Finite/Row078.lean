/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row078_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1057288098254840047043924/129626609677734375:ℝ),(27120548045867470409054452/1166639487099609375:ℝ),(25733118794835590546397056/1166639487099609375:ℝ),(1625632726652336112147584/233327897419921875:ℝ)],
![(675878312157394145206006/43208869892578125:ℝ),(51813802692766328108127218/1166639487099609375:ℝ),(1958427620765005526043904/46665579483984375:ℝ),(15395602254608451963532544/1166639487099609375:ℝ)],
![(3917510934943956639061501/518506438710937500:ℝ),(99740999165923587098127589/4666557948398437500:ℝ),(23467743053642796817857344/1166639487099609375:ℝ),(7346892865785802481213824/1166639487099609375:ℝ)]]
theorem row078_identity (δ p : ℝ) : rowMargin .oldSwitch .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (57397600513951581884483/17398189039288320000000000:ℝ) row078_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row078_coefficients,Fin.sum_univ_succ]
 ring
theorem row078_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capC δ p := by
 rw [row078_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row078_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row078_pos
