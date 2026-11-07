/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row057_coefficients : Fin 3 → Fin 4 → ℝ := ![![(25918100426520910913899878097475768265031/199329309247934435625000000000:ℝ),(77360035835254248330221499556685770411189/199329309247934435625000000000:ℝ),(20990901847019201539741552200819090489253/54362538885800300625000000000:ℝ),(76574111895386309471188186721379988943309/597987927743803306875000000000:ℝ)],
![(25702450995778747194951884967010952793271/99664654623967217812500000000:ℝ),(25571266827264987432760928545431893919367/33221551541322405937500000000:ℝ),(228963360358598233321825972767826699059451/298993963871901653437500000000:ℝ),(75929309691028332698519095604972512164961/298993963871901653437500000000:ℝ)],
![(25488041174795123703209609844722974410991/199329309247934435625000000000:ℝ),(76071280474225951171158604586177937042437/199329309247934435625000000000:ℝ),(5045287466115662502341369985337924116769/13288620616528962375000000000:ℝ),(25096071951135587715237053246113899120089/199329309247934435625000000000:ℝ)]]
theorem row057_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (25096071951135587715237053246113899120089/389626476932732589652920238080000000000000:ℝ) row057_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row057_coefficients,Fin.sum_univ_succ]
 ring
theorem row057_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row057_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row057_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row057_pos
