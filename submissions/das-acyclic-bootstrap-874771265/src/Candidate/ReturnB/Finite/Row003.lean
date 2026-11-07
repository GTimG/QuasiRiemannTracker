/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row003_coefficients : Fin 3 → Fin 4 → ℝ := ![![(899106267904085795931305221757/142209169833071477812500000:ℝ),(167356450340317842789902786297/9480611322204765187500000:ℝ),(2330727325377844494168859064239/142209169833071477812500000:ℝ),(239800777662229676488874163847/47403056611023825937500000:ℝ)],
![(215093667850062790792261646639/23701528305511912968750000:ℝ),(1762571041131026254419974174551/71104584916535738906250000:ℝ),(1598052858760119583231300733251/71104584916535738906250000:ℝ),(160212021131190424336870499539/23701528305511912968750000:ℝ)],
![(438426202465714272875430221077/142209169833071477812500000:ℝ),(1160199707147954858181672581447/142209169833071477812500000:ℝ),(1014838775863388626204371045013/142209169833071477812500000:ℝ),(97625044834194132877292894881/47403056611023825937500000:ℝ)]]
theorem row003_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (97625044834194132877292894881/690357048457790545920000000000:ℝ) row003_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row003_coefficients,Fin.sum_univ_succ]
 ring
theorem row003_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row003_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row003_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row003_pos
