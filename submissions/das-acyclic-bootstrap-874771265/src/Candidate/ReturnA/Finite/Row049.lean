/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row049_coefficients : Fin 3 → Fin 4 → ℝ := ![![(808321831929053791344694730066579726051143/747489813779776939593750000000:ℝ),(53754365673313253091921706549197206717257/16610884750661709768750000000:ℝ),(2412933702778563684793047101536026279250517/747489813779776939593750000000:ℝ),(5943030199025763201196517837694308911297/5536961583553903256250000000:ℝ)],
![(267217083553032194987926015685235176155309/124581635629962823265625000000:ℝ),(479789158493371242382883323463530269353233/74748981377977693959375000000:ℝ),(2392944139221862501907652948850863259136453/373744906889888469796875000000:ℝ),(5893700702647029707747890391769758821009/2768480791776951628125000000:ℝ)],
![(795017753369722353882130934119955564657423/747489813779776939593750000000:ℝ),(67973037977181313864603852686675128462039/21356851822279341131250000000:ℝ),(2373065722825474976206860710509621918307087/747489813779776939593750000000:ℝ),(1948215171408090694589728879280118485909/1845653861184634418750000000:ℝ)]]
theorem row049_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (17533936542672816251307559913521066373181/259752688796438647480228878745600000000000:ℝ) row049_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (255/512:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row049_coefficients,Fin.sum_univ_succ]
 ring
theorem row049_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row049_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row049_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row049_pos
