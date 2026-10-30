/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row123_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7198983720200486136349509272372332196/1532107964309842402998046875:ℝ),(12693228857737453909805134849778375612/919264778585905441798828125:ℝ),(62152645396332839000410943313120198656/4596323892929527208994140625:ℝ),(20283431265456641343646052553220317184/4596323892929527208994140625:ℝ)],
![(14257342316489542420301025279872789116/1532107964309842402998046875:ℝ),(25130583367385962553610013587423528484/919264778585905441798828125:ℝ),(123012308131697394928613004764980535296/4596323892929527208994140625:ℝ),(40131375965891924874685488370606260224/4596323892929527208994140625:ℝ)],
![(1412643096053621351106692749042946629/306421592861968480599609375:ℝ),(12446072195390060892575078356834580927/919264778585905441798828125:ℝ),(12180625607797046268520918206386157568/919264778585905441798828125:ℝ),(3972478445279950659947099092774166528/919264778585905441798828125:ℝ)]]
theorem row123_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (484921685214837727044323619723409/219345120021730277726355456000000000:ℝ) row123_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row123_coefficients,Fin.sum_univ_succ]
 ring
theorem row123_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row123_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row123_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row123_pos
