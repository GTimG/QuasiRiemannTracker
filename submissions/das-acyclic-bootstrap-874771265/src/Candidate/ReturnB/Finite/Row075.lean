/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row075_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5617377308698224786842/388879829033203125:ℝ),(45355654093822190320546/1166639487099609375:ℝ),(40663381746055519287614/1166639487099609375:ℝ),(12159859578328003327594/1166639487099609375:ℝ)],
![(1928289742649441748113/77775965806640625:ℝ),(75212323493881936521287/1166639487099609375:ℝ),(64762544294283981855964/1166639487099609375:ℝ),(18474566940143671556372/1166639487099609375:ℝ)],
![(71629487111600171631743/6222077264531250000:ℝ),(540975462573076741437181/18666231793593750000:ℝ),(1117464700342711719518/46665579483984375:ℝ),(7556179931175528829078/1166639487099609375:ℝ)]]
theorem row075_identity (δ p : ℝ) : rowMargin .oldSwitch .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (3778089965587764414539/1087386814955520000000000:ℝ) row075_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row075_coefficients,Fin.sum_univ_succ]
 ring
theorem row075_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capC δ p := by
 rw [row075_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row075_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row075_pos
