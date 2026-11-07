/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row203_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10376732298350959698090713198113286365712/2417012448450378685524052734375:ℝ),(28987823625732737652976603282835264351792/2417012448450378685524052734375:ℝ),(8952170658236668666015974195980432889616/805670816150126228508017578125:ℝ),(2748469967885248294064518158670606894256/805670816150126228508017578125:ℝ)],
![(20199323601439461989596291743847907431712/2417012448450378685524052734375:ℝ),(56281801268477120667931203556222551307616/2417012448450378685524052734375:ℝ),(17329298339069136292626397021185735134432/805670816150126228508017578125:ℝ),(5301798573820224085689421425118978842464/805670816150126228508017578125:ℝ)],
![(131754358685990311641330829125585017152/32226832646005049140320703125:ℝ),(9156890163252465038429433047563533663008/805670816150126228508017578125:ℝ),(8435937461344783878825920929732395396916/805670816150126228508017578125:ℝ),(95292690249686686268076249240579096304/29839659857412082537333984375:ℝ)]]
theorem row203_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (53602138265448761025792890197825741671/262472423856842583435473227612160000000000:ℝ) row203_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (255/512:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row203_coefficients,Fin.sum_univ_succ]
 ring
theorem row203_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row203_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row203_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row203_pos
