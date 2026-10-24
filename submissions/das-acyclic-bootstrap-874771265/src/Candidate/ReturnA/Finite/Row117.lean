/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row117_coefficients : Fin 3 → Fin 4 → ℝ := ![![(791703484091856218084315564210008253/18385295571718108835976562500:ℝ),(327123640600453230241757969298248881/2626470795959729833710937500:ℝ),(88240453878452176724668344475093799/735411822868724353439062500:ℝ),(33706868173740539776808813261886241/875490265319909944570312500:ℝ)],
![(764253590956585874970041755851031373/9192647785859054417988281250:ℝ),(88230345363350554717858982349257359/367705911434362176719531250:ℝ),(2120181206038804573382234260068374531/9192647785859054417988281250:ℝ),(32317662528553607990960972663712949/437745132659954972285156250:ℝ)],
![(744276135475706533147523679053317493/18385295571718108835976562500:ℝ),(2143943133813105053825494446855878983/18385295571718108835976562500:ℝ),(2056517271824570624721991911808934837/18385295571718108835976562500:ℝ),(31278327882010661983012009089589207/875490265319909944570312500:ℝ)]]
theorem row117_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (31278327882010661983012009089589207/13369607315610226451892142080000000000:ℝ) row117_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row117_coefficients,Fin.sum_univ_succ]
 ring
theorem row117_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row117_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row117_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row117_pos
