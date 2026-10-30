/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row200_coefficients : Fin 3 → Fin 4 → ℝ := ![![(487705386106931699882466550463390261/1149592885820226025763642578125:ℝ),(1154808010496464429291585374025462417/1149592885820226025763642578125:ℝ),(5143339070677228480722461196465985231/6897557314921356154581855468750:ℝ),(228077516914986664800561980971835459/1379511462984271230916371093750:ℝ)],
![(984049247856527020738319995013161726/1149592885820226025763642578125:ℝ),(2298660080917543923765688386962112362/1149592885820226025763642578125:ℝ),(185291846900496894724598854525222894/127732542868914002862626953125:ℝ),(6416327011220085459604608301646462/20901688833095018650248046875:ℝ)],
![(112282362876651065680330101129475243/229918577164045205152728515625:ℝ),(267408297103719338717612031495572129/229918577164045205152728515625:ℝ),(600961044958237726053672018309480587/689755731492135615458185546875:ℝ),(135546041195027501926320592836189929/689755731492135615458185546875:ℝ)]]
theorem row200_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3208163505610042729802304150823231/9974674441034611951480602624000000000:ℝ) row200_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row200_coefficients,Fin.sum_univ_succ]
 ring
theorem row200_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row200_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row200_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row200_pos
