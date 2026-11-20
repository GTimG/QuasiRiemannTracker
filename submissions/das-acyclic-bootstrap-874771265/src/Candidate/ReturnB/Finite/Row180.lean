/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row180_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11041133952650624390803331901371657/5425572705713203860000000000000:ℝ),(120394093072211846953504254443813359/27127863528566019300000000000000:ℝ),(879052552778476366683906070866735343/298406498814226212300000000000000:ℝ),(160973165799789850881135025385229529/298406498814226212300000000000000:ℝ)],
![(4146012885013269608596812761080801843/746016247035565530750000000000000:ℝ),(1879775934208773161436287745970482773/149203249407113106150000000000000:ℝ),(606171474091169445337194364806188959/67819658821415048250000000000000:ℝ),(1408979045491424455274067037046466527/746016247035565530750000000000000:ℝ)],
![(34178653302901903648658095338319903727/7460162470355655307500000000000000:ℝ),(83641985061085635548360271232595187629/7460162470355655307500000000000000:ℝ),(66567890683346778177569601961248605653/7460162470355655307500000000000000:ℝ),(17068316624277986808764756024673321751/7460162470355655307500000000000000:ℝ)]]
theorem row180_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (160973165799789850881135025385229529/139067507955833806572748800000000000000:ℝ) row180_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row180_coefficients,Fin.sum_univ_succ]
 ring
theorem row180_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row180_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row180_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row180_pos
