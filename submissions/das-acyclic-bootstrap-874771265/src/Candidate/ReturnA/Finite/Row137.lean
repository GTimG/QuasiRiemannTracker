/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row137_coefficients : Fin 3 → Fin 4 → ℝ := ![![(178996205522523991672857745738432261/4778429025739399645517578125:ℝ),(512415231344856870890520069419093557/4778429025739399645517578125:ℝ),(488252625601077615011645464733881856/4778429025739399645517578125:ℝ),(30966422218435405796676555554394112/955685805147879929103515625:ℝ)],
![(354407469342277348416327571514465156/4778429025739399645517578125:ℝ),(202596796850089185957469199115936628/955685805147879929103515625:ℝ),(963585625617776727060198375652390912/4778429025739399645517578125:ℝ),(305006060717615770760145060962172928/4778429025739399645517578125:ℝ)],
![(35469756346486916096672254870107044/955685805147879929103515625:ℝ),(506349084617531966166042030929009908/4778429025739399645517578125:ℝ),(481081316706789154247401335304288256/4778429025739399645517578125:ℝ),(152079451630671283844971000600813568/4778429025739399645517578125:ℝ)]]
theorem row137_identity (δ p : ℝ) : rowMargin .newSwitch .P δ p =
 Record12518109.Bernstein.bsum 2 3 (18564386185384678203731811596779/8907637322833274173685760000000000:ℝ) row137_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row137_coefficients,Fin.sum_univ_succ]
 ring
theorem row137_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .P δ p := by
 rw [row137_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row137_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row137_pos
