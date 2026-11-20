/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row065_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8027742798073526260356405473011895483/7786352226872676454101562500:ℝ),(71532955993318346467086253889776118897/23359056680618029362304687500:ℝ),(1967206869925649749595734969477651352/648862685572723037841796875:ℝ),(5842428555312197657583761607613754056/5839764170154507340576171875:ℝ)],
![(62140184229440409383600131630207337839/31145408907490705816406250000:ℝ),(553569190095059131907209175623203705421/93436226722472117449218750000:ℝ),(34243923116323490870309544812977002416/5839764170154507340576171875:ℝ),(11297130461201745142623128829690646672/5839764170154507340576171875:ℝ)],
![(480854789905915557287005726446348904307/498326542519851293062500000000:ℝ),(611782536915588847627997061272169717407/213568518222793411312500000000:ℝ),(16552629075071109474047295068081073032/5839764170154507340576171875:ℝ),(1819738652226701217644843115706527848/1946588056718169113525390625:ℝ)]]
theorem row065_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (227467331528337652205605389463315981/3715792018839435302928384000000000000:ℝ) row065_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row065_coefficients,Fin.sum_univ_succ]
 ring
theorem row065_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row065_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row065_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row065_pos
