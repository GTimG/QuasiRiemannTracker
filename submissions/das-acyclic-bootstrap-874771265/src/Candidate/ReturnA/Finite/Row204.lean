/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row204_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1397465923772355427297430200211463636295168/362554294719123619498601455078125:ℝ),(3874351998260098323636627173668191759964672/362554294719123619498601455078125:ℝ),(711592128986725838993978618249524144242688/72510858943824723899720291015625:ℝ),(1081072958894977397426141801306642597543936/362554294719123619498601455078125:ℝ)],
![(2707116762779314910577198223343300307211904/362554294719123619498601455078125:ℝ),(7480587199492021907877157207278738409722752/362554294719123619498601455078125:ℝ),(977593413400291963139288245443521743814656/51793470674160517071228779296875:ℝ),(2069680212782901719881679649668026604191744/362554294719123619498601455078125:ℝ)],
![(1318459236244193238646492337808954881415736/362554294719123619498601455078125:ℝ),(726524186610017956400477276689466201002376/72510858943824723899720291015625:ℝ),(3311539586973010247281509164437321180209152/362554294719123619498601455078125:ℝ),(997376257341835549999999987454597400363008/362554294719123619498601455078125:ℝ)]]
theorem row204_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (3804688481681196403503417920893087007/21627206095041409048995016212480000000000:ℝ) row204_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row204_coefficients,Fin.sum_univ_succ]
 ring
theorem row204_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row204_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row204_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row204_pos
