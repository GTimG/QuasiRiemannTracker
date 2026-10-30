/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row010_coefficients : Fin 3 → Fin 4 → ℝ := ![![(361025989908845729572861277/105404418281250000:ℝ),(3231062450159384267791331351/316213254843750000:ℝ),(66935792022429382847525888/6587776142578125:ℝ),(66558346040235206100530944/19763328427734375:ℝ)],
![(174478903893188569903576123/26351104570312500:ℝ),(141932521642068800060084147/7186664882812500:ℝ),(388054774829453052680465408/19763328427734375:ℝ),(128599518233655279942916096/19763328427734375:ℝ)],
![(16854041561585937444516937/5270220914062500:ℝ),(68538491383727217445890613/7186664882812500:ℝ),(187355485902657777049547264/19763328427734375:ℝ),(6897476717039466054476288/2195925380859375:ℝ)]]
theorem row010_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (13471634212967707137649/65496025661440000000000:ℝ) row010_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row010_coefficients,Fin.sum_univ_succ]
 ring
theorem row010_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row010_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row010_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row010_pos
