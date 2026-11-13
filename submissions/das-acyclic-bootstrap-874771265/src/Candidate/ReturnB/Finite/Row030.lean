/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row030_coefficients : Fin 3 → Fin 4 → ℝ := ![![(783534841336323842631421691312348/346057828555441728515625:ℝ),(20942996368485846412065677435390396/3114520456998975556640625:ℝ),(6910477999856708705385349857141632/1038173485666325185546875:ℝ),(6840250146796313367538354857845632/3114520456998975556640625:ℝ)],
![(503455181644290146314130688906281/115352609518480576171875:ℝ),(40359416015163763546484893633605139/3114520456998975556640625:ℝ),(39940735989920311029751884178011392/3114520456998975556640625:ℝ),(2634921542741375109453430703975168/622904091399795111328125:ℝ)],
![(75079126331764492980751471579229/35722098431529468750000:ℝ),(310878034832624023784966877244982663/49832327311983608906250000:ℝ),(19222761758675835329896747591085696/3114520456998975556640625:ℝ),(192086206027173600250723842690176/94379407787847744140625:ℝ)]]
theorem row030_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1500673484587293751958780021017/11259901940684826869760000000000:ℝ) row030_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row030_coefficients,Fin.sum_univ_succ]
 ring
theorem row030_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row030_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row030_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row030_pos
