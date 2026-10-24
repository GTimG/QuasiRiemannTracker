/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row187_coefficients : Fin 3 → Fin 4 → ℝ := ![![(74772723475409231502940285337031846289/932526194188619046262500000000000:ℝ),(29205204989489325683091912797539359701/186505238837723809252500000000000:ℝ),(1139612499506490651336652991882185673/14570721784197172597851562500000:ℝ),(12706266625467734187293709676400827/7285360892098586298925781250000:ℝ)],
![(44527700838749464375483061421195341567/233131548547154761565625000000000:ℝ),(92148785946339371343721723015803070439/233131548547154761565625000000000:ℝ),(208698594627715330588902100472015581/910670111512323287365722656250:ℝ),(90260712356927148917666444008498201/3642680446049293149462890625000:ℝ)],
![(27480580950630564011134816581818852881/233131548547154761565625000000000:ℝ),(60478201218124966829691503020782472681/233131548547154761565625000000000:ℝ),(1247783477050069449851946836403709669/7285360892098586298925781250000:ℝ),(216132003231225490567160711366858269/7285360892098586298925781250000:ℝ)]]
theorem row187_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (12706266625467734187293709676400827/434588705154455735579443200000000000000:ℝ) row187_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row187_coefficients,Fin.sum_univ_succ]
 ring
theorem row187_pos {δ p : ℝ} (hd : δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row187_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row187_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row187_pos
