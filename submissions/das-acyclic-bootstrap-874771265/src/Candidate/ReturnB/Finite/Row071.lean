/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row071_coefficients : Fin 3 → Fin 4 → ℝ := ![![(146900505813430597090292748391/33578723049928073201250000000:ℝ),(392263345230098824835581695253/33578723049928073201250000000:ℝ),(343825173019905858400285145333/33578723049928073201250000000:ℝ),(98462333603237630654996198471/33578723049928073201250000000:ℝ)],
![(40484612801947649893609300927/16789361524964036600625000000:ℝ),(101035393531906820771592940129/16789361524964036600625000000:ℝ),(84972971109223820870590758977/16789361524964036600625000000:ℝ),(88807965015507818154934981/61052223727141951275000000:ℝ)],
![(68383611990176995501925853463/33578723049928073201250000000:ℝ),(1931263341699054705596058031/610522237271419512750000000:ℝ),(49287867634042073236343889371/33578723049928073201250000000:ℝ),(6917744622133490865486551129/33578723049928073201250000000:ℝ)]]
theorem row071_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6917744622133490865486551129/1910256244618130386560000000000:ℝ) row071_coefficients (0/1:ℝ) (3/8:ℝ) (0/1:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row071_coefficients,Fin.sum_univ_succ]
 ring
theorem row071_pos {δ p : ℝ} (hd : δ∈Set.Icc (0/1:ℝ) (3/8:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row071_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row071_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row071_pos
