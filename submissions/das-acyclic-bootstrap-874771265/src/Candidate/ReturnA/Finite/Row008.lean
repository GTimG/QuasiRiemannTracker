/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row008_coefficients : Fin 3 → Fin 4 → ℝ := ![![(988315690852850441569973/2195925410156250:ℝ),(79193291758554909149356247/59289986074218750:ℝ),(39167727432547304297006288/29644993037109375:ℝ),(516533735191333227340912/1185799721484375:ℝ)],
![(11476037486605112551972531/13175552460937500:ℝ),(306423413251468193896184651/118579972148437500:ℝ),(3030037649995434459730336/1185799721484375:ℝ),(24966172281880316261150432/29644993037109375:ℝ)],
![(44392869796517119260329879/105404419687500000:ℝ),(1184938351969742425409861711/948639777187500000:ℝ),(36603429930021549854332592/29644993037109375:ℝ),(12059601061237538852242192/29644993037109375:ℝ)]]
theorem row008_identity (δ p : ℝ) : rowMargin .oldSmall .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (753725066327346178265137/3536785432903680000000000:ℝ) row008_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row008_coefficients,Fin.sum_univ_succ]
 ring
theorem row008_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capC δ p := by
 rw [row008_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row008_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row008_pos
