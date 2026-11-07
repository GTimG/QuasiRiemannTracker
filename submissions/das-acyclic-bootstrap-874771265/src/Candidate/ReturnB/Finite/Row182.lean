/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row182_coefficients : Fin 3 → Fin 4 → ℝ := ![![(672247935398316958037455527411992207/1698581914652080694531250000000:ℝ),(1545143374966266349728842917443723941/1698581914652080694531250000000:ℝ),(1090936069672432644549827866529730727/1698581914652080694531250000000:ℝ),(217914788781965685257389538851123993/1698581914652080694531250000000:ℝ)],
![(152564585058789063872510298067370269/169858191465208069453125000000:ℝ),(8944909697991788589366908460992129653/4246454786630201736328125000000:ℝ),(13077229497139219962456068303898786319/8492909573260403472656250000000:ℝ),(2814318020208661517536731439990852963/8492909573260403472656250000000:ℝ)],
![(9405701198825482798250647032889686863/16985819146520806945312500000000:ℝ),(14320652879781387082393503115060673621/10616136966575504340820312500000:ℝ),(71200044719088611509976070634369925221/67943276586083227781250000000000:ℝ),(85825607407333203222269462396565869993/339716382930416138906250000000000:ℝ)]]
theorem row182_identity (δ p : ℝ) : rowMargin .newTop .P δ p =
 Record12518109.Bernstein.bsum 2 3 (217914788781965685257389538851123993/810594863667527755707187200000000000000:ℝ) row182_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row182_coefficients,Fin.sum_univ_succ]
 ring
theorem row182_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .P δ p := by
 rw [row182_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row182_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row182_pos
