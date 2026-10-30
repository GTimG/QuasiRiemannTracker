/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row066_coefficients : Fin 3 → Fin 4 → ℝ := ![![(398736342497945541927724327843746254021/388552580911924602609375000000:ℝ),(78961985687771194495882935821311123067/25903505394128306840625000000:ℝ),(2345408844141590206428128492030861501123/777105161823849205218750000000:ℝ),(51601451579732289404809079038601354477/51807010788256613681250000000:ℝ)],
![(128606008524866247757572793382972477509/64758763485320767101562500000:ℝ),(229150969079542010381507683526911116149/38855258091192460260937500000:ℝ),(567055040145789984082433050604767112759/97138145227981150652343750000:ℝ),(1247243886035092003227469754079653591/647587634853207671015625000:ℝ)],
![(373206797632660748673809538930427613779/388552580911924602609375000000:ℝ),(8863996434851002889615545449650184037/3108420647295396820875000000:ℝ),(1096433765919688185534985423396927390291/388552580911924602609375000000:ℝ),(24109394148620149648268467074738799963/25903505394128306840625000000:ℝ)]]
theorem row066_identity (δ p : ℝ) : rowMargin .oldPeak .P δ p =
 Record12518109.Bernstein.bsum 2 3 (24109394148620149648268467074738799963/395572296958366820651866521600000000000:ℝ) row066_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row066_coefficients,Fin.sum_univ_succ]
 ring
theorem row066_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .P δ p := by
 rw [row066_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row066_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row066_pos
