/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row118_coefficients : Fin 3 → Fin 4 → ℝ := ![![(458804286232493349578126129820867683/367703503162504997519531250:ℝ),(1350019879709764701244107716888638121/367703503162504997519531250:ℝ),(1323846976997301680317342363676190793/367703503162504997519531250:ℝ),(86526194860771749822150532071684071/73540700632500999503906250:ℝ)],
![(89893771036953298467967157456247079/36770350316250499751953125:ℝ),(1321743219240273044341281202640759273/183851751581252498759765625:ℝ),(1295302627273927635021487485923026561/183851751581252498759765625:ℝ),(13646059632833103007171635149225893/5930701663911370927734375:ℝ)],
![(441308980297717448500604310501907307/367703503162504997519531250:ℝ),(51879331224439492080924889659046913/14708140126500199900781250:ℝ),(1270265085122673999055524049430091379/367703503162504997519531250:ℝ),(414590364753538270343209456190200861/367703503162504997519531250:ℝ)]]
theorem row118_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (414590364753538270343209456190200861/179686345467174859409970954240000000000:ℝ) row118_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row118_coefficients,Fin.sum_univ_succ]
 ring
theorem row118_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row118_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row118_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row118_pos
