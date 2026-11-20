/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row059_coefficients : Fin 3 → Fin 4 → ℝ := ![![(153031147171426441491114450044369115791651/298993963871901653437500000000:ℝ),(91348514741149536680232864419034484789511/59798792774380330687500000000:ℝ),(161362544564447208562016848224449642816/106176833761328712158203125:ℝ),(588615213047170355276842316994128460992/1167945171374615833740234375:ℝ)],
![(15238819915043666832837593655284997000013/14949698193595082671875000000:ℝ),(227407938875406123295315476790229627131009/74748490967975413359375000000:ℝ),(3534940506906847064709170234247386834944/1167945171374615833740234375:ℝ),(1172224233208390809776571034559033051648/1167945171374615833740234375:ℝ)],
![(12645592109401258231297333390518262932953/24916163655991804453125000000:ℝ),(503216376787195833322497402009216088043/332215515413224059375000000:ℝ),(586658068155578436371827226750290310272/389315057124871944580078125:ℝ),(64846249175699632728852707581227271808/129771685708290648193359375:ℝ)]]
theorem row059_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (506611321685153380694161777978338061/7926970966242118116311040000000000000:ℝ) row059_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row059_coefficients,Fin.sum_univ_succ]
 ring
theorem row059_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row059_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row059_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row059_pos
