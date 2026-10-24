/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row121_coefficients : Fin 3 → Fin 4 → ℝ := ![![(290969574812731883741097193279611479/61283917193750832919921875:ℝ),(82783324820007922187414815830363727/5930701663911370927734375:ℝ),(2514283002698296427356803882537817088/183851751581252498759765625:ℝ),(820907828479632873607312401440063488/183851751581252498759765625:ℝ)],
![(115185122621738054911935997033963292/12256783438750166583984375:ℝ),(5077904373413195984276277670719333524/183851751581252498759765625:ℝ),(4973369659192480435329377096628932608/183851751581252498759765625:ℝ),(1623240455792433744757103295012798464/183851751581252498759765625:ℝ)],
![(285150311932915829653469581439640956/61283917193750832919921875:ℝ),(2513364825672124090829434871237791012/183851751581252498759765625:ℝ),(492165050640102788932209706378399744/36770350316250499751953125:ℝ),(802910523215405592412429080441880576/183851751581252498759765625:ℝ)]]
theorem row121_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (24502884619610766370008211683407/10967184171580496790159360000000000:ℝ) row121_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row121_coefficients,Fin.sum_univ_succ]
 ring
theorem row121_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row121_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row121_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row121_pos
