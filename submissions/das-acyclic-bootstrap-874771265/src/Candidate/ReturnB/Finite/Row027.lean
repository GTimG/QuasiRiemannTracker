/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row027_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11991704566589885650070972547197/3950254717585318828125000:ℝ),(314361215870862863032337467386319/35552292458267869453125000:ℝ),(27734110387130940203504714943029/3232026587115260859375000:ℝ),(32879603776481996646482299970591/11850764152755956484375000:ℝ)],
![(94873347131817598655429059918549/17776146229133934726562500:ℝ),(25046494859719592235233267672173/1616013293557630429687500:ℝ),(266535431349795043983709898216659/17776146229133934726562500:ℝ),(5726450270100841461495075916087/1185076415275595648437500:ℝ)],
![(300595781849703520803768501967/129281063484610434375000:ℝ),(658956719805134660878360279549/97940199609553359375000:ℝ),(20958808395083917552824927918359/3232026587115260859375000:ℝ),(2242691030146203717006187914139/1077342195705086953125000:ℝ)]]
theorem row027_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2242691030146203717006187914139/16066491309563125432320000000000:ℝ) row027_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row027_coefficients,Fin.sum_univ_succ]
 ring
theorem row027_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row027_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row027_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row027_pos
