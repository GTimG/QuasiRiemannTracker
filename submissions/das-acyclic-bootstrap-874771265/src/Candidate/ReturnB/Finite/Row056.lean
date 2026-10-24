/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row056_coefficients : Fin 3 → Fin 4 → ℝ := ![![(627355577181018586235519279952768440347/149496981935950826718750000000:ℝ),(207050134409721361983143503542633049091/16610775770661202968750000000:ℝ),(4804469560869279869861245340613214412/389315057124871944580078125:ℝ),(4756410508538093436593265479410510412/1167945171374615833740234375:ℝ)],
![(1234261593400233031218592077391303475939/149496981935950826718750000000:ℝ),(244379247918528514610664254992321633261/9966465462396721781250000000:ℝ),(28349647017153275626960407526250640488/1167945171374615833740234375:ℝ),(3118040161038809151722905047829585832/389315057124871944580078125:ℝ)],
![(2428088918536310365134435442820454050923/597987927743803306875000000000:ℝ),(2403447328267030089417052021836608151929/199329309247934435625000000000:ℝ),(13938951869218730642021246622715718108/1167945171374615833740234375:ℝ),(4598612777087864026068655997345854036/1167945171374615833740234375:ℝ)]]
theorem row056_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1149653194271966006517163999336463509/17835684674044765761699840000000000000:ℝ) row056_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row056_coefficients,Fin.sum_univ_succ]
 ring
theorem row056_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row056_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row056_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row056_pos
