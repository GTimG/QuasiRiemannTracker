/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row041_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13630806151144008691845880204027/8888073114566967363281250:ℝ),(3617380385567957372506955711893/808006646778815214843750:ℝ),(15481922718518764902172019523241/3555229245826786945312500:ℝ),(8362902997994617445408100370871/5925382076377978242187500:ℝ)],
![(3328325598236261999345724377153/1212009970168222822265625:ℝ),(106592673329212992618888303690037/13332109671850451044921875:ℝ),(459545122444676689073618193814/59253820763779782421875:ℝ),(3712923715270362830761615479644/1481345519094494560546875:ℝ)],
![(6538489863518521571787558127747/5332843868740180417968750:ℝ),(18978418167043330400832910133041/5332843868740180417968750:ℝ),(6117091041132556308645041379697/1777614622913393472656250:ℝ),(218936661114592522612179060511/197512735879265941406250:ℝ)]]
theorem row041_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (218936661114592522612179060511/2945523406753239662592000000000:ℝ) row041_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row041_coefficients,Fin.sum_univ_succ]
 ring
theorem row041_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row041_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row041_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row041_pos
