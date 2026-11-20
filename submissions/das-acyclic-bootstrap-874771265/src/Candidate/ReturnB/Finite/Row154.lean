/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row154_coefficients : Fin 3 → Fin 4 → ℝ := ![![(105582738446253543292419973710501664118539/65353953345574829343750000000000:ℝ),(1299735803570278587765177243344069983330213/326769766727874146718750000000000:ℝ),(1017223515552696120671003040450101849057573/326769766727874146718750000000000:ℝ),(1817777411072055751311098705384025824593/2420516790576845531250000000000:ℝ)],
![(19893548045281576453506502617016882329359/6535395334557482934375000000000:ℝ),(1205870041480877783701437619709588819114917/163384883363937073359375000000000:ℝ),(921226436453234171673435582044236598932277/163384883363937073359375000000000:ℝ),(4726525173811057000746566832380266123363/3630775185865268296875000000000:ℝ)],
![(94943889864759891587965650814985871722467/65353953345574829343750000000000:ℝ),(1135835785394823831830304331974422802118693/326769766727874146718750000000000:ℝ),(849025211496006632788797764324804895203963/326769766727874146718750000000000:ℝ),(4175720055893841156185226349458302294669/7261550371730536593750000000000:ℝ)]]
theorem row154_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (4175720055893841156185226349458302294669/113552484542561567064746622976000000000000000:ℝ) row154_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (255/512:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row154_coefficients,Fin.sum_univ_succ]
 ring
theorem row154_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row154_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row154_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row154_pos
