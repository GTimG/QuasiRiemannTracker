/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row165_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2555490686105378943973387457907102475520957/7294061701522912460185546875000:ℝ),(20869884568564676178939554960038248855124961/25529215955330193610649414062500:ℝ),(238639285879899209977587314442889564823748601/408467455285283097770390625000000:ℝ),(498214380016619153020056117351704643182627/4254869325888365601774902343750:ℝ)],
![(5108924553602053689799734237769915320954661/7294061701522912460185546875000:ℝ),(16678215073240215661985732763047597212183561/10211686382132077444259765625000:ℝ),(23810454903233173253465599408153234203713167/20423372764264154888519531250000:ℝ),(566548860667353298153996786024898238966187/2431353900507637486728515625000:ℝ)],
![(25647230511990859070998384556723763641253719/72940617015229124601855468750000:ℝ),(418882902550314078962241037053437057482966219/510584319106603872212988281250000:ℝ),(37416402193241227312374939539413524749362909/63823039888325484026623535156250:ℝ),(19992963350866013862373555169658391489169987/170194773035534624070996093750000:ℝ)]]
theorem row165_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (566548860667353298153996786024898238966187/77865561033471987133185692994109440000000000000:ℝ) row165_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1023/2048:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row165_coefficients,Fin.sum_univ_succ]
 ring
theorem row165_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1023/2048:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row165_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row165_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row165_pos
