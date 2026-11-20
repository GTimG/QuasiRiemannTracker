/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row053_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3324660090373036114598209937486956038401/24916163655991804453125000000:ℝ),(29772568438916053190044372561346591596291/74748490967975413359375000000:ℝ),(462867408051091384776444505959377325088/1167945171374615833740234375:ℝ),(51171487951772128548276033509189715232/389315057124871944580078125:ℝ)],
![(127632591125240743706844074813181968143/482248328825647828125000000:ℝ),(3936730595716633780307848688218733518747/4983232731198360890625000000:ℝ),(61201459295161277361921187354775366336/77863011424974388916015625:ℝ),(60892165897394332072317709069051731136/233589034274923166748046875:ℝ)],
![(1569525583861641253319815390368707150987/11959758554876066137500000000:ℝ),(187390590879893206829509612464457663043/478390342195042645500000000:ℝ),(18207046765805412569634803233387333472/46717806854984633349609375:ℝ),(6038143522069260591068243819353214624/46717806854984633349609375:ℝ)]]
theorem row053_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (188691985064664393470882619354787957/2853709547847162521871974400000000000:ℝ) row053_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row053_coefficients,Fin.sum_univ_succ]
 ring
theorem row053_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row053_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row053_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row053_pos
