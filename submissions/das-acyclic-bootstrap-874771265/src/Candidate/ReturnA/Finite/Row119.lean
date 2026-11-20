/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row119_coefficients : Fin 3 → Fin 4 → ℝ := ![![(173918964820409697200382170216654496149/4596323892929527208994140625:ℝ),(516566046257036442149837098558979399359/4596323892929527208994140625:ℝ),(511397083051628796660195587717305476671/4596323892929527208994140625:ℝ),(18749997906021811661550858458331174829/510702654769947467666015625:ℝ)],
![(343996665804956232671345519255813468074/4596323892929527208994140625:ℝ),(1021555294939175056483924873573896813182/4596323892929527208994140625:ℝ),(1011164628654355167342067967410587277342/4596323892929527208994140625:ℝ),(5295332671893709869351158272301649718/72957522109992495380859375:ℝ)],
![(972538664000249981651029112824580579/26264707959597298337109375:ℝ),(72191207174316496612348840850917131289/656617698989932458427734375:ℝ),(71445179119488810710650927216581176603/656617698989932458427734375:ℝ),(2036691964016512032800749081057637883/56744739418883051962890625:ℝ)]]
theorem row119_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (18330227676148608295206741729518740947/7986112103191175267263572869120000000000:ℝ) row119_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (255/512:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row119_coefficients,Fin.sum_univ_succ]
 ring
theorem row119_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row119_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row119_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row119_pos
