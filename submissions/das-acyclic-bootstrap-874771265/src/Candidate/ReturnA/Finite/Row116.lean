/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row116_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2570523511045359185592351169076/1525196382913322138671875:ℝ),(310315665618520598848617217926656/65583444465272851962890625:ℝ),(289662650430358499148465180253333/65583444465272851962890625:ℝ),(17975259757178082906597148456889/13116688893054570392578125:ℝ)],
![(210589681230703587500846110741648/65583444465272851962890625:ℝ),(587259687599957907098891525148496/65583444465272851962890625:ℝ),(544065518672605309039165727963048/65583444465272851962890625:ℝ),(6695551271005792777869375042248/2623337778610914078515625:ℝ)],
![(20778937225233828737865054475576/13116688893054570392578125:ℝ),(57668884409889487281897570669928/13116688893054570392578125:ℝ),(53138480842336016457475526763128/13116688893054570392578125:ℝ),(16247825181027076861402385568776/13116688893054570392578125:ℝ)]]
theorem row116_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2030978147628384607675298196097/782440969826053074714624000000000:ℝ) row116_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row116_coefficients,Fin.sum_univ_succ]
 ring
theorem row116_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row116_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row116_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row116_pos
