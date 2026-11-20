/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row065_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9633205016062310781229892571836053507/9343561370996926669921875000:ℝ),(9537641631594281723840352174190357057/3114520456998975556640625000:ℝ),(114223882834925025292184968795768252/37675650689503736572265625:ℝ),(389491702731238225113177950442312868/389315057124871944580078125:ℝ)],
![(74567551715704541743551361893698491031/37374245483987706679687500000:ℝ),(8200951116242563506690718852163399989/1384231314221766914062500000:ℝ),(2282907543693579673767028681077583448/389315057124871944580078125:ℝ),(2259405554426609656656572461522959448/1167945171374615833740234375:ℝ)],
![(577020560082737363100252918767982340603/597987927743803306875000000000:ℝ),(570991879130011255639169940065118822569/199329309247934435625000000000:ℝ),(3310495797871357861887927128868655388/1167945171374615833740234375:ℝ),(99257568067493180800931358496693436/106176833761328712158203125:ℝ)]]
theorem row065_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (24814392016873295200232839624173359/405356469864653767311360000000000000:ℝ) row065_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row065_coefficients,Fin.sum_univ_succ]
 ring
theorem row065_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row065_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row065_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row065_pos
