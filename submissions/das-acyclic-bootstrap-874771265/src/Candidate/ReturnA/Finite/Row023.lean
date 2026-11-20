/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row023_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12535188114330282640892490253479214924/11123360324103823505859375:ℝ),(785612158135325665897853918564283273788/233590566806180293623046875:ℝ),(781515869874312212282282233120295102464/233590566806180293623046875:ℝ),(51828531439115425767494949588315068416/46718113361236058724609375:ℝ)],
![(24953208685059606251570221532971194386/11123360324103823505859375:ℝ),(1563853422893212633486602360381323352826/233590566806180293623046875:ℝ),(1555671520175333735211509020793240489984/233590566806180293623046875:ℝ),(515835469748388801977466197198062219264/233590566806180293623046875:ℝ)],
![(347708164962647247930669372073658878861/311454089074907058164062500:ℝ),(3112997362556876460772267308149556586727/934362267224721174492187500:ℝ),(154832745361455150099768629264567619584/46718113361236058724609375:ℝ),(256695504914353878474282159125849360384/233590566806180293623046875:ℝ)]]
theorem row023_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (125339602008961854723770585510668633/891790084521464472702812160000000000:ℝ) row023_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row023_coefficients,Fin.sum_univ_succ]
 ring
theorem row023_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row023_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row023_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row023_pos
