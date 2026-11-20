/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row067_coefficients : Fin 3 → Fin 4 → ℝ := ![![(785478140689531396413812012837037486733/777105161823849205218750000000:ℝ),(2333090899014957006029716103217311910541/777105161823849205218750000000:ℝ),(18045738901556470844176842306548304704/6071134076748821915771484375:ℝ),(5955012783323762063310772166858660768/6071134076748821915771484375:ℝ)],
![(379901349307301128639078839852904662089/194276290455962301304687500000:ℝ),(1128113465061906220657093197020867992649/194276290455962301304687500000:ℝ),(775400739200029148527415880812637056/134914090594418264794921875:ℝ),(767426779240616298540957028546320896/404742271783254794384765625:ℝ)],
![(183684547863037886197432459875045292117/194276290455962301304687500000:ℝ),(545298128973222932910845177108295180373/194276290455962301304687500000:ℝ),(16861562311243283418169364093102706112/6071134076748821915771484375:ℝ),(5561136386445761203956079570188647104/6071134076748821915771484375:ℝ)]]
theorem row067_identity (δ p : ℝ) : rowMargin .oldPeak .P δ p =
 Record12518109.Bernstein.bsum 2 3 (86892756038215018811813743284197611/1448629017181519118598144000000000000:ℝ) row067_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row067_coefficients,Fin.sum_univ_succ]
 ring
theorem row067_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .P δ p := by
 rw [row067_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row067_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row067_pos
