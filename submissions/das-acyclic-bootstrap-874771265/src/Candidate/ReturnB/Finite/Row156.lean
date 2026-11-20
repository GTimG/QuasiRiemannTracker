/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row156_coefficients : Fin 3 → Fin 4 → ℝ := ![![(26650409509314970322908685502116420234093/108923255575958048906250000000000:ℝ),(167773044939691097408883061956456463677259/326769766727874146718750000000000:ℝ),(94187889291431770884203989935780106103/319111100320189596405029296875:ℝ),(8422958313398964917266972211370876208/319111100320189596405029296875:ℝ)],
![(12853970341985819465666127931256278874929/27230813893989512226562500000000:ℝ),(79373350173133795982643803389549860893159/81692441681968536679687500000000:ℝ),(169692763224119838582978035050139107276/319111100320189596405029296875:ℝ),(10270183476125200623605339175178398464/319111100320189596405029296875:ℝ)],
![(6274240248938205548757737720066690094917/27230813893989512226562500000000:ℝ),(7634741500978008383618380683017459033687/16338488336393707335937500000000:ℝ),(78400944541637687676935934088755276188/319111100320189596405029296875:ℝ),(2809695265559450954389036590546737824/319111100320189596405029296875:ℝ)]]
theorem row156_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (87802977048732842324657393454585557/19492575853024560996679680000000000000000:ℝ) row156_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row156_coefficients,Fin.sum_univ_succ]
 ring
theorem row156_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row156_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row156_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row156_pos
