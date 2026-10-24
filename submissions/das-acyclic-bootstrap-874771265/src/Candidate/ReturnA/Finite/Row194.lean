/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row194_coefficients : Fin 3 → Fin 4 → ℝ := ![![(32030827930351675801145464/5112420843147275390625:ℝ),(695494517563926490146751496/46011787588325478515625:ℝ),(546133940126732514377806264/46011787588325478515625:ℝ),(138916873935971106441363944/46011787588325478515625:ℝ)],
![(31023226471314096073059428/3067452505888365234375:ℝ),(1010363874049130279666081212/46011787588325478515625:ℝ),(668337743699696739402444464/46011787588325478515625:ℝ),(123322266720277900832254672/46011787588325478515625:ℝ)],
![(305595360441789987919547467/61349050117767304687500:ℝ),(1865135715647541959797621889/184047150353301914062500:ℝ),(2150453307359537932118528/368094300706603828125:ℝ),(31719254839399242505071128/46011787588325478515625:ℝ)]]
theorem row194_identity (δ p : ℝ) : rowMargin .newKink .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (3964906854924905313133891/10721523596047994880000000000:ℝ) row194_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row194_coefficients,Fin.sum_univ_succ]
 ring
theorem row194_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capC δ p := by
 rw [row194_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row194_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row194_pos
