/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row018_coefficients : Fin 3 → Fin 4 → ℝ := ![![(609936254441003332444408560576503749/2076346971332650371093750:ℝ),(1092298694504271035108719151767324963/1245808182799590222656250:ℝ),(905602671780452689999498626339359744/1038173485666325185546875:ℝ),(900965645084958158453130332183272448/3114520456998975556640625:ℝ)],
![(3626236669632934289300503002079236137/6229040913997951113281250:ℝ),(2164597277748325364753980793548108021/1245808182799590222656250:ℝ),(5383686844415041809248233104812275712/3114520456998975556640625:ℝ),(1785311953342900282556026404012873728/3114520456998975556640625:ℝ)],
![(1437199748288506951592938256776575187/4983232731198360890625000:ℝ),(1429788872339241383602085713349131409/1661077577066120296875000:ℝ),(533397302986164068091496387098628096/622904091399795111328125:ℝ),(58958813740922097142083785133571072/207634697133265037109375:ℝ)]]
theorem row018_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (57576966543869235490316196419503/396348548312105905815552000000000:ℝ) row018_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row018_coefficients,Fin.sum_univ_succ]
 ring
theorem row018_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row018_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row018_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row018_pos
