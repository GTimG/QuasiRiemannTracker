/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row058_coefficients : Fin 3 → Fin 4 → ℝ := ![![(533612554197643667976624782066846110061/1038180296916356860546875000:ℝ),(23889899225202906856981032777940435372387/15572704453745352908203125000:ℝ),(1273259175643758543037865482877244816704/834252024307786762939453125:ℝ),(2955672551650384330546140501601559821376/5839764170154507340576171875:ℝ)],
![(95647254918922150574211256862024250128171/93436226722472117449218750000:ℝ),(285471122033413452042342285974932332764971/93436226722472117449218750000:ℝ),(142001868521750546581820013979912267648/46718113361236058724609375:ℝ),(8720358071832775489339480572631153024/8651502474302973837890625:ℝ)],
![(380981635826646635562928908067455331003537/747489813779776939593750000000:ℝ),(45482708274261278364344689068327858112313/29899592551191077583750000000:ℝ),(2945842591824769686959194257590147920448/1946588056718169113525390625:ℝ),(418657894177580510585881454560687142464/834252024307786762939453125:ℝ)]]
theorem row058_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (6541529596524695477904397727510736601/101918866802453082594607104000000000000:ℝ) row058_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row058_coefficients,Fin.sum_univ_succ]
 ring
theorem row058_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row058_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row058_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row058_pos
