/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row049_coefficients : Fin 3 → Fin 4 → ℝ := ![![(323325819266357914482058557991565230635749/298993963871901653437500000000:ℝ),(193513970808657463606964057730620939231779/59798792774380330687500000000:ℝ),(107240529496398125233097851163638636515959/33221551541322405937500000000:ℝ),(792396863394163720699389193410390773137/738256700918275687500000000:ℝ)],
![(320657609647252234114714467531295436154661/149496981935950826718750000000:ℝ),(191913931515434495679767084125403080769699/29899396387190165343750000000:ℝ),(319056336237266381429006977858409502542293/49832327311983608906250000000:ℝ),(785819653726363353657817611134588987489/369128350459137843750000000:ℝ)],
![(9636491924093702503842878729397948168733/9060423147633383437500000000:ℝ),(63440929370791589528174519404651977468593/19932930924793443562500000000:ℝ),(316405903481417201244551776317039032202047/99664654623967217812500000000:ℝ),(2337837054429925190619715240020146104781/2214770102754827062500000000:ℝ)]]
theorem row049_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2337837054429925190619715240020146104781/34633464616242896858037354496000000000000:ℝ) row049_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (255/512:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row049_coefficients,Fin.sum_univ_succ]
 ring
theorem row049_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row049_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row049_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row049_pos
