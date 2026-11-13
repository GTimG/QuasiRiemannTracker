/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row011_coefficients : Fin 3 → Fin 4 → ℝ := ![![(135404289539940926429319859461614/1481345519094494560546875:ℝ),(1199699362049054734073492138460664/4444036557283483681640625:ℝ),(787255720691026327648392283017893/2962691038188989121093750:ℝ),(154958739710505011623630517655407/1777614622913393472656250:ℝ)],
![(253249764561807049665412821632104/1481345519094494560546875:ℝ),(2241985537826163568900311370846424/4444036557283483681640625:ℝ),(2204974015711160843545206097944412/4444036557283483681640625:ℝ),(28909490792833999461183890179772/177761462291339347265625:ℝ)],
![(23626035485789589230938514007148/296269103818898912109375:ℝ),(208970807264065354110362160209132/888807311456696736328125:ℝ),(205332739424488434816992582028932/888807311456696736328125:ℝ),(22413328600682600795901779613748/296269103818898912109375:ℝ)]]
theorem row011_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5603332150170650198975444903437/35346280881038875951104000000000:ℝ) row011_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row011_coefficients,Fin.sum_univ_succ]
 ring
theorem row011_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row011_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row011_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row011_pos
