/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row013_coefficients : Fin 3 → Fin 4 → ℝ := ![![(142096823901773690700528465100360645753/1868724534449442348984375000:ℝ),(424165940518400652901734500955038904811/1868724534449442348984375000:ℝ),(422045543649407609886250501192939321163/1868724534449442348984375000:ℝ),(27995284948960571790479501967652212421/373744906889888469796875000:ℝ)],
![(27912214225375342956884603075601905669/186872453444944234898437500:ℝ),(59509900252050204838441212152162575549/133480323889245882070312500:ℝ),(59208505372095547867014971104965063893/133480323889245882070312500:ℝ),(137451304649111356347415438922626946753/934362267224721174492187500:ℝ)],
![(137046846503937981890924317946277535537/1868724534449442348984375000:ℝ),(16361490143119710557482941646832694163/74748981377977693959375000:ℝ),(406938127869415605358356277437583373489/1868724534449442348984375000:ℝ),(134947718446776974732590745494293554951/1868724534449442348984375000:ℝ)]]
theorem row013_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (134947718446776974732590745494293554951/913193046549979620047679651840000000000:ℝ) row013_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row013_coefficients,Fin.sum_univ_succ]
 ring
theorem row013_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row013_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row013_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row013_pos
