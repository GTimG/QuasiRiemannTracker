/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row194_coefficients : Fin 3 → Fin 4 → ℝ := ![![(96091478853950548283404756/15337260259537587890625:ℝ),(231828570220738752934196876/15337260259537587890625:ℝ),(182041790166128458938008084/15337260259537587890625:ℝ),(46304698799340254287215964/15337260259537587890625:ℝ)],
![(31022851688917764001458434/3067452051907517578125:ℝ),(336782495703932666085736922/15337260259537587890625:ℝ),(222773944811954545665778184/15337260259537587890625:ℝ),(41105707552610699587333432/15337260259537587890625:ℝ)],
![(67909304198005455174984043/13633120230700078125000:ℝ),(414467834609151647219981281/40899360692100234375000:ℝ),(1194663507164374752171136/204496803460501171875:ℝ),(3524097427217458592399756/5112420086512529296875:ℝ)]]
theorem row194_identity (δ p : ℝ) : rowMargin .newKink .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (881024356804364648099939/2382560446504427520000000000:ℝ) row194_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row194_coefficients,Fin.sum_univ_succ]
 ring
theorem row194_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capC δ p := by
 rw [row194_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row194_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row194_pos
