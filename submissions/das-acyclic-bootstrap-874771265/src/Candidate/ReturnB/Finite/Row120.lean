/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row120_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6853510161527002175989260526388795776/183851751581252498759765625:ℝ),(20354646385612074290376905585751090304/183851751581252498759765625:ℝ),(4029927045170612585461820955456372736/36770350316250499751953125:ℝ),(214467683333407988833556241465147392/5930701663911370927734375:ℝ)],
![(13551260730307482922388204032375984928/183851751581252498759765625:ℝ),(40239915037353525579673350879109223264/183851751581252498759765625:ℝ),(39827804377574539343779909759102418944/183851751581252498759765625:ℝ),(13139148422894963747818103917994180608/183851751581252498759765625:ℝ)],
![(6702393403979461415217733870565258902/183851751581252498759765625:ℝ),(3979835491468149350470441733659201082/36770350316250499751953125:ℝ),(19692058289378052818376364495453835264/183851751581252498759765625:ℝ),(6495273406780153864078965927527776256/183851751581252498759765625:ℝ)]]
theorem row120_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (99110006817324125123275236931271/43868736686321987160637440000000000:ℝ) row120_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row120_coefficients,Fin.sum_univ_succ]
 ring
theorem row120_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row120_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row120_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row120_pos
