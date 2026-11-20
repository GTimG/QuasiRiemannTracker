/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row022_coefficients : Fin 3 → Fin 4 → ℝ := ![![(91710300176300462762727861612927691/321498885883765218750000:ℝ),(42425476503350336664429690971840034779/49832327311983608906250000:ℝ),(426324368395835738603989309475891057/503356841535187968750000:ℝ),(4665244077155175437553550207925657323/16610775770661202968750000:ℝ)],
![(14083302035335584827270601617444879993/24916163655991804453125000:ℝ),(42030660381086222568388543190054808827/24916163655991804453125000:ℝ),(334494914753231570702886754935916531/199329309247934435625000:ℝ),(13864505733035884211961513198129637541/24916163655991804453125000:ℝ)],
![(13952081622663867989033333235241881281/49832327311983608906250000:ℝ),(1665502666389764918598274236243905603/1993293092479344356250000:ℝ),(41419338771139137312821625396431014657/49832327311983608906250000:ℝ),(13733853467011917291453539777450255863/49832327311983608906250000:ℝ)]]
theorem row022_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (13733853467011917291453539777450255863/97406619233183147413230059520000000000:ℝ) row022_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row022_coefficients,Fin.sum_univ_succ]
 ring
theorem row022_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row022_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row022_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row022_pos
