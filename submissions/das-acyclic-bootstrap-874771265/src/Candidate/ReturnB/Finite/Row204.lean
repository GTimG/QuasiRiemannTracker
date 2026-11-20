/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row204_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3105224982301838056470356781406952138752/805670816150126228508017578125:ℝ),(8608914192324590385588650624252244209408/805670816150126228508017578125:ℝ),(4743497940102192021752022849567805014016/483402489690075737104810546875:ℝ),(7206411326770219960436754692095648858112/2417012448450378685524052734375:ℝ)],
![(222789207505681615203744395207098864128/29839659857412082537333984375:ℝ),(16622023190351746795945163265946209387328/805670816150126228508017578125:ℝ),(45616560116674167964538705815531182424064/2417012448450378685524052734375:ℝ),(13796394724870060465730497053641937256448/2417012448450378685524052734375:ℝ)],
![(2929657651158130291643897352231980844704/805670816150126228508017578125:ℝ),(1614348680470845716763989463090090787564/161134163230025245701603515625:ℝ),(237362483936180166490321611315826290688/25989381166133104145419921875:ℝ),(2216147622324950766832220106759290355712/805670816150126228508017578125:ℝ)]]
theorem row204_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (16907864550208669790895233968805621/96120272408511688269826621440000000000:ℝ) row204_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row204_coefficients,Fin.sum_univ_succ]
 ring
theorem row204_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row204_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row204_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row204_pos
