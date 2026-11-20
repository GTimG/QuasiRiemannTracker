/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row025_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1773817733160763761556892193258972823/49832327311983608906250000:ℝ),(5266783647420421034134890629869917527/49832327311983608906250000:ℝ),(65154240689747480732538266561795072/622904091399795111328125:ℝ),(35820272372357836262093748754326272/1038173485666325185546875:ℝ)],
![(219676897697099894597154205685449748/3114520456998975556640625:ℝ),(652214733979598743451993056525843732/3114520456998975556640625:ℝ),(4164044898864153172145419224449024/20093680367735326171875:ℝ),(212889089450631679564234091449204736/3114520456998975556640625:ℝ)],
![(21763554873846791372961795831283904/622904091399795111328125:ℝ),(5873712973566972966740065559792192/56627644672708646484375:ℝ),(2367920115878014729156663407149056/23070521903696115234375:ℝ),(21086551913108867481299586666594304/622904091399795111328125:ℝ)]]
theorem row025_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (160877623848792018747708028157/1161177387633122770944000000000:ℝ) row025_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row025_coefficients,Fin.sum_univ_succ]
 ring
theorem row025_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row025_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row025_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row025_pos
