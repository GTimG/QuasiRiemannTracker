/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row173_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10171028981750151162040586677061691090496034401/680779092142138496283984375000000:ℝ),(872049366022406091461909515590010109868132829/29176246806091649840742187500000:ℝ),(477620955150100680035873388249204050718883328/31911519944162742013311767578125:ℝ),(116781217288964876993118229927581219356672/6382303988832548402662353515625:ℝ)],
![(1272342443142027752178798182545652759771536031/42548693258883656017749023437500:ℝ),(763729603091688935260172636492296447303536629/12764607977665096805324707031250:ℝ),(956505595528614996263825756655786372729806848/31911519944162742013311767578125:ℝ),(287668626555675319960837840362449561583616/6382303988832548402662353515625:ℝ)],
![(159294768149305641938462816759692456754525281/10637173314720914004437255859375:ℝ),(191340631735068227011630351706559843480876566/6382303988832548402662353515625:ℝ),(480067563658567491781466651177971759209807872/31911519944162742013311767578125:ℝ),(249734180837914218415367454857520107159552/6382303988832548402662353515625:ℝ)]]
theorem row173_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1781939961074293167009250334588336477/199606540735218717016223089950720000000000000:ℝ) row173_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row173_coefficients,Fin.sum_univ_succ]
 ring
theorem row173_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row173_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row173_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row173_pos
