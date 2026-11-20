/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row031_coefficients : Fin 3 → Fin 4 → ℝ := ![![(29080538804925384324021056154521993/12951670955478568242187500:ℝ),(28791640802615161684755298313196947/4317223651826189414062500:ℝ),(171023711485975737276755869974402431/25903341910957136484375000:ℝ),(3762329026787264112112839556117649/1726889460730475765625000:ℝ)],
![(345875074475708957802544860020843/79948586144929433593750:ℝ),(83189921647235737376106105061196317/6475835477739284121093750:ℝ),(8233584686916816961215022133787031/647583547773928412109375:ℝ),(4526966951171549242739897020977046/1079305912956547353515625:ℝ)],
![(26970040554039430711768889728386223/12951670955478568242187500:ℝ),(80061392054479144211977697514593093/12951670955478568242187500:ℝ),(79216327234444740703607592279715567/12951670955478568242187500:ℝ),(8708323691885467448387753789502899/4317223651826189414062500:ℝ)]]
theorem row031_identity (δ p : ℝ) : rowMargin .oldSmall .P δ p =
 Record12518109.Bernstein.bsum 2 3 (8708323691885467448387753789502899/65928300067950841634488320000000000:ℝ) row031_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row031_coefficients,Fin.sum_univ_succ]
 ring
theorem row031_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .P δ p := by
 rw [row031_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row031_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row031_pos
