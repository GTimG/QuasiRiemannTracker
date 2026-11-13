/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row015_coefficients : Fin 3 → Fin 4 → ℝ := ![![(554862315554520286586278747453291975904/233590566806180293623046875:ℝ),(1660362659309584130574601921921450555616/233590566806180293623046875:ℝ),(331228499195526945655564639263393726464/46718113361236058724609375:ℝ),(550642151078581989923176544098810052608/233590566806180293623046875:ℝ)],
![(1099645455274904434091538904133675071912/233590566806180293623046875:ℝ),(3290509108683638567127380009068366578856/233590566806180293623046875:ℝ),(3282090112589814852185188273245659365376/233590566806180293623046875:ℝ),(1091226456878050444964511745998467858432/233590566806180293623046875:ℝ)],
![(1089609352412364736274510565211799895391/467181133612360587246093750:ℝ),(652084424532395549618249820561343959731/93436226722472117449218750:ℝ),(232287461567957642599617004280087339008/33370080972311470517578125:ℝ),(540605844691806097715660880854557671424/233590566806180293623046875:ℝ)]]
theorem row015_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (32995962200427618268778129934970561/222947521130366118175703040000000000:ℝ) row015_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row015_coefficients,Fin.sum_univ_succ]
 ring
theorem row015_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row015_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row015_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row015_pos
