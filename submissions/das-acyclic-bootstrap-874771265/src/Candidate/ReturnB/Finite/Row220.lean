/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row220_coefficients : Fin 3 → Fin 4 → ℝ := ![![(47745558181313064267130611132026454853/5025548934391732999832285156250:ℝ),(120951156091153321991835625262927147383/5025548934391732999832285156250:ℝ),(33029484758087594111481171633654225919/1675182978130577666610761718750:ℝ),(8627097662983749154653958828484203409/1675182978130577666610761718750:ℝ)],
![(52333747026796784238680179681056619133/2512774467195866499916142578125:ℝ),(26812761683490592922626154961361730587/502554893439173299983228515625:ℝ),(12395452437102180385360624439470828619/279197163021762944435126953125:ℝ),(368239617736828523554043299625205849/31021907002418104937236328125:ℝ)],
![(19639643737955535062561949622397587471/1675182978130577666610761718750:ℝ),(51044173882542850107793326411054678029/1675182978130577666610761718750:ℝ),(8663403718578071378017967106781121809/335036595626115533322152343750:ℝ),(11911941592397562391130525919936018487/1675182978130577666610761718750:ℝ)]]
theorem row220_identity (δ p : ℝ) : rowMargin .newKink .P δ p =
 Record12518109.Bernstein.bsum 2 3 (8627097662983749154653958828484203409/25581710598708317495755423088640000000000:ℝ) row220_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row220_coefficients,Fin.sum_univ_succ]
 ring
theorem row220_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newKink .P δ p := by
 rw [row220_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row220_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row220_pos
