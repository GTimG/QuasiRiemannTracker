/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row068_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10308291250260659837668727216197/2222018337931727519531250:ℝ),(89748091904146223799557466174227/6666055013795182558593750:ℝ),(43386333443102604357084393064478/3333027506897591279296875:ℝ),(2794914571199306354379007972832/666605501379518255859375:ℝ)],
![(1938944216281828757973169554974/222201833793172751953125:ℝ),(84255601735398517358386641238586/3333027506897591279296875:ℝ),(9034557294015834440683821900488/370336389655287919921875:ℝ),(26139259704559337337165142940416/3333027506897591279296875:ℝ)],
![(4555445699707023610803402461834/1111009168965863759765625:ℝ),(7902957012137213344345302640622/666605501379518255859375:ℝ),(38057307653002626450056303374264/3333027506897591279296875:ℝ),(1356521489765382480070572645184/370336389655287919921875:ℝ)]]
theorem row068_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (21195648277584101251102697581/345178533439273943040000000000:ℝ) row068_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row068_coefficients,Fin.sum_univ_succ]
 ring
theorem row068_pos {δ p : ℝ} (hd : δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row068_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row068_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row068_pos
