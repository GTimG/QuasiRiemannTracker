/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row156_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1332622545939844485306433812233058220158133/5446232737137107970271875000000000:ℝ),(1677902780160363735461923997962663059941707/3267739642282264782163125000000000:ℝ),(1345765931485081529456712491058178334834/4558788563451820287615966796875:ℝ),(168556714654035517488568604390157518432/6382303988832548402662353515625:ℝ)],
![(642749318850240540071548250779996112277017/1361558184284276992567968750000000:ℝ),(793819203597831439297135630825061631747047/816934910570566195540781250000000:ℝ),(16972401720498933997738287065353047256408/31911519944162742013311767578125:ℝ),(205597336155381372299118081796910388736/6382303988832548402662353515625:ℝ)],
![(44819622946677676878250690038347327218699/194508312040610998938281250000000:ℝ),(54539972747004084847364000181006548393461/116704987224366599362968750000000:ℝ),(1120235963202892557989010973186395801416/4558788563451820287615966796875:ℝ),(8041474513138825221528268132000262336/911757712690364057523193359375:ℝ)]]
theorem row156_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (125648039267794144086379189562504099/27846894633819575476593623040000000000000:ℝ) row156_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row156_coefficients,Fin.sum_univ_succ]
 ring
theorem row156_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row156_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row156_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row156_pos
