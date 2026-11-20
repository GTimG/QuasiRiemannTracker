/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row149_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3733719807830409460549844763004517/518386295875781250000000000:ℝ),(357380898383331300445063533984781/20735451835031250000000000:ℝ),(13407668719543540462776162718820011/1036772591751562500000000000:ℝ),(200404227735852957441511703039333/69118172783437500000000000:ℝ)],
![(3524684628050392988561828314333703/259193147937890625000000000:ℝ),(1646074494316710119355114990998453/51838629587578125000000000:ℝ),(185105478521710284135250117586551/8099785873059082031250000:ℝ),(40589582305385716137141904070369/8639771597929687500000000:ℝ)],
![(3595122589757323236807481298650787/518386295875781250000000000:ℝ),(334448752014625809100288558834153/20735451835031250000000000:ℝ),(5974502966294641999358504755125923/518386295875781250000000000:ℝ),(80560450379088000577251472194859/34559086391718750000000000:ℝ)]]
theorem row149_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (80560450379088000577251472194859/527751629625140183040000000000000000:ℝ) row149_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row149_coefficients,Fin.sum_univ_succ]
 ring
theorem row149_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row149_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row149_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row149_pos
