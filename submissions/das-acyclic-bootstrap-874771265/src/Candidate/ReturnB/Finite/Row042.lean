/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row042_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4006480987732882774555600120537/75891181162500000000000:ℝ),(3966635571656441539196482310201/25297060387500000000000:ℝ),(436328409911099998097350359161/2810784487500000000000:ℝ),(3887441340363258105594612887281/75891181162500000000000:ℝ)],
![(3778299846911873911233471926857/37945590581250000000000:ℝ),(3738443105580207745755878453209/12648530193750000000000:ℝ),(11096275864944636748402628923919/37945590581250000000000:ℝ),(1219748798371962474122821830383/12648530193750000000000:ℝ)],
![(3559663969183848588292639181617/75891181162500000000000:ℝ),(391088724660519291855419924417/2810784487500000000000:ℝ),(2088067375239208372382303038013/15178236232500000000000:ℝ),(3440605279545869570107816412423/75891181162500000000000:ℝ)]]
theorem row042_identity (δ p : ℝ) : rowMargin .oldPeak .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (3440605279545869570107816412423/36216682349749862400000000000000:ℝ) row042_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row042_coefficients,Fin.sum_univ_succ]
 ring
theorem row042_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .capP δ p := by
 rw [row042_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row042_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row042_pos
