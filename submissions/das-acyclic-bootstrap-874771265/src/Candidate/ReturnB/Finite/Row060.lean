/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row060_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1942163878442717743512000943120333519951/119597585548760661375000000000:ℝ),(9612608629673733732942448478603921052121/199329309247934435625000000000:ℝ),(18583662404234534960040971313568613192/389315057124871944580078125:ℝ),(18393548305841926096781417656115809192/1167945171374615833740234375:ℝ)],
![(12038019636680912385195814430929594633/373742454839877066796875000:ℝ),(19859129813854874501176575806109326597/207634697133265037109375000:ℝ),(22112782987464434064739829911276542464/233589034274923166748046875:ℝ),(270186017472751951129529197638316544/8651445713886043212890625:ℝ)],
![(746131006260572162809018955230624822/46717806854984633349609375:ℝ),(67135085045739076201623247583542646/1415691116817716162109375:ℝ),(2192625650371674402728832429359263744/46717806854984633349609375:ℝ),(723298674219564692527929214332981248/46717806854984633349609375:ℝ)]]
theorem row060_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (176586590385635911261701468343013/2786825730319494650265600000000000:ℝ) row060_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row060_coefficients,Fin.sum_univ_succ]
 ring
theorem row060_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row060_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row060_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row060_pos
