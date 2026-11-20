/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row052_coefficients : Fin 3 → Fin 4 → ℝ := ![![(187614397506032527209553073130054706289/5536925256887067656250000000:ℝ),(1680195729874883206561765221255761652899/16610775770661202968750000000:ℝ),(6018766542502311719956932882095625408841/59798792774380330687500000000:ℝ),(9981486779356762252815049178147371431629/298993963871901653437500000000:ℝ)],
![(184550399314694685157179945863774653099/2768462628443533828125000000:ℝ),(4957950097497101413285689988582351908349/24916163655991804453125000000:ℝ),(3699819643454843724635638879577390055767/18687122741993853339843750000:ℝ),(2454144465382715209946655287317210065847/37374245483987706679687500000:ℝ)],
![(60506944909253579434988550719320765613/1845641752295689218750000000:ℝ),(4876241841842121933089717530965504842357/49832327311983608906250000000:ℝ),(88208634455684007405511959604671833657/906042314763338343750000000:ℝ),(536306840392953502038265041404368893443/16610775770661202968750000000:ℝ)]]
theorem row052_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (536306840392953502038265041404368893443/8117218269431928951102504960000000000000:ℝ) row052_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row052_coefficients,Fin.sum_univ_succ]
 ring
theorem row052_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row052_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row052_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row052_pos
