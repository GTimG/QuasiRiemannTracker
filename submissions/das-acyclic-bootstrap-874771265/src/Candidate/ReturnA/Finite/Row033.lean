/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row033_coefficients : Fin 3 → Fin 4 → ℝ := ![![(67727918333620994846864454820307/6666055013795182558593750:ℝ),(196551954753592036916094933316379/6666055013795182558593750:ℝ),(95009091978968508680483725449056/3333027506897591279296875:ℝ),(6119371081782884271845642552704/666605501379518255859375:ℝ)],
![(12621958351230564057496494595954/666605501379518255859375:ℝ),(182817256255148187796028317988522/3333027506897591279296875:ℝ),(176404422050848640764224661638784/3333027506897591279296875:ℝ),(56696500035519134369384910380032/3333027506897591279296875:ℝ)],
![(29325905142331597316998813774054/3333027506897591279296875:ℝ),(16956507015436319393768120945534/666605501379518255859375:ℝ),(81637573444991759889642967257728/3333027506897591279296875:ℝ),(26180703858728639868790082554112/3333027506897591279296875:ℝ)]]
theorem row033_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (102268374448158749487461259977/776651700238366371840000000000:ℝ) row033_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row033_coefficients,Fin.sum_univ_succ]
 ring
theorem row033_pos {δ p : ℝ} (hd : δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row033_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row033_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row033_pos
