/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row019_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7252045314479926899025299863209983007/24916163655991804453125000:ℝ),(801665659414844339896781905119196013/922820876147844609375000:ℝ),(244704907256349308486837286612800512/283138223363543232421875:ℝ),(892638027743505474763832849419454464/3114520456998975556640625:ℝ)],
![(1796392679164148269597246285733596667/3114520456998975556640625:ℝ),(5361458277951541070926147300743545819/3114520456998975556640625:ℝ),(1777931381695427886125717023885205504/1038173485666325185546875:ℝ),(117915234291451572082276856588877824/207634697133265037109375:ℝ)],
![(32960107569611559480778946412697994/115352609518480576171875:ℝ),(2655944354952383193915264979043923022/3114520456998975556640625:ℝ),(528429570224715573245937125722750976/622904091399795111328125:ℝ),(876126384484157439498680704587677696/3114520456998975556640625:ℝ)]]
theorem row019_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (53474510771738124969401898473369/371576764042599286702080000000000:ℝ) row019_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row019_coefficients,Fin.sum_univ_succ]
 ring
theorem row019_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row019_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row019_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row019_pos
