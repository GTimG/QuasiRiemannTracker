/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row023_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11817578755896996603916744665220862/10486600865316416015625:ℝ),(129317700337116471335019408086619918/38450869839493525390625:ℝ),(10420116846951504221888764505056769024/3114520456998975556640625:ℝ),(22291638349818492366991038499910656/20093680367735326171875:ℝ)],
![(6986835156395405457551761974729358421/3114520456998975556640625:ℝ),(20851189738726853151207962289342337141/3114520456998975556640625:ℝ),(20742098295081845401603927058848876544/3114520456998975556640625:ℝ),(2292581193494643297840174899016132608/1038173485666325185546875:ℝ)],
![(27816401243354817319603492475754075631/24916163655991804453125000:ℝ),(83012509511570885945697174739230300239/24916163655991804453125000:ℝ),(688139275599165185394860484232736768/207634697133265037109375:ℝ),(311143230374359355424115857703291904/283138223363543232421875:ℝ)]]
theorem row023_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (303850810912460308031363142288371/2161901172611486758993920000000000:ℝ) row023_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row023_coefficients,Fin.sum_univ_succ]
 ring
theorem row023_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row023_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row023_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row023_pos
