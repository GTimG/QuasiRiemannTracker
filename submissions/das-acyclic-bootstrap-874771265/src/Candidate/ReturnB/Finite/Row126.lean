/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row126_coefficients : Fin 3 → Fin 4 → ℝ := ![![(28400482223833520202492970332829426/183851751581252498759765625:ℝ),(16352433462793367354192562302688314/36770350316250499751953125:ℝ),(2528407015206997152515583786033152/5930701663911370927734375:ℝ),(25018716862655834605058635405165568/183851751581252498759765625:ℝ)],
![(55927924606870636599964364288280866/183851751581252498759765625:ℝ),(160832649953052928023617500138693586/183851751581252498759765625:ℝ),(153998356525417912589611172026215424/183851751581252498759765625:ℝ),(49093194615861439530011496644552704/183851751581252498759765625:ℝ)],
![(11040365857231791893965029226188181/73540700632500999503906250:ℝ),(158579312177969481126829190861213057/367703503162504997519531250:ℝ),(75835677267106714560257584033478912/183851751581252498759765625:ℝ),(24146714741031195082782634598030336/183851751581252498759765625:ℝ)]]
theorem row126_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (23580776114288276448029916599639/10967184171580496790159360000000000:ℝ) row126_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row126_coefficients,Fin.sum_univ_succ]
 ring
theorem row126_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row126_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row126_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row126_pos
