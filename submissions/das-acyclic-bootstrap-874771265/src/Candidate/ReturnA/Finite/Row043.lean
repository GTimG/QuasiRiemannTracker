/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row043_coefficients : Fin 3 → Fin 4 → ℝ := ![![(239780199282200056697135967017/1185799721484375000000:ℝ),(3559658957855612536159192218893/5928998607421875000000:ℝ),(110086555616363997816821692991/185281206481933593750:ℝ),(4034763257913318324530492333/20586800720214843750:ℝ)],
![(1550993891837839611514545754691/3952665738281250000000:ℝ),(4603590959750427865805105512771/3952665738281250000000:ℝ),(21348801175779398255497638299/18528120648193359375:ℝ),(7039752419939140813510639433/18528120648193359375:ℝ)],
![(18053375416199850052629170064821/94863977718750000000000:ℝ),(10713493031544223897927544033777/18972795543750000000000:ℝ),(11496828009791839018522745737/20586800720214843750:ℝ),(34107995561717821797547387211/185281206481933593750:ℝ)]]
theorem row043_identity (δ p : ℝ) : rowMargin .oldPeak .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (34107995561717821797547387211/353678543290368000000000000000:ℝ) row043_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row043_coefficients,Fin.sum_univ_succ]
 ring
theorem row043_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .capC δ p := by
 rw [row043_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row043_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row043_pos
