/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row050_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6291391129156051692767509888709030250161/5839764170154507340576171875:ℝ),(18827247823615580169642706406206534733489/5839764170154507340576171875:ℝ),(18780371324977092105006104364317360379392/5839764170154507340576171875:ℝ),(6244514610673477262195477153069855896064/5839764170154507340576171875:ℝ)],
![(49914911407552849691167285034683850614483/23359056680618029362304687500:ℝ),(21338574936720726025948860191792088329173/3337008097231147051757812500:ℝ),(4138769682045284868704030086075139075072/648862685572723037841796875:ℝ),(4128382937028408854764981109132853251072/1946588056718169113525390625:ℝ)],
![(396008066041886657910775776887236077894329/373744906889888469796875000000:ℝ),(1185032053343337582592157269569569254719161/373744906889888469796875000000:ℝ),(18469422921353567263108659596051485714432/5839764170154507340576171875:ℝ),(877274728523192128120679507190205153792/834252024307786762939453125:ℝ)]]
theorem row050_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1713427204146859625235702162480869441/25479716700613270648651776000000000000:ℝ) row050_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row050_coefficients,Fin.sum_univ_succ]
 ring
theorem row050_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row050_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row050_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row050_pos
