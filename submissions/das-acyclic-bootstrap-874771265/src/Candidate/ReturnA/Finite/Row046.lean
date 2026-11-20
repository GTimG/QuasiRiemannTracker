/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row046_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15231653397279423327286092597092/370336389655287919921875:ℝ),(404954805606925874128103068625176/3333027506897591279296875:ℝ),(44300141799472447448746609272127/370336389655287919921875:ℝ),(26166245427660235151949882452059/666605501379518255859375:ℝ)],
![(28668503747720566636197378203312/370336389655287919921875:ℝ),(761578140968773562033565262304816/3333027506897591279296875:ℝ),(749201696631757093754908866417208/3333027506897591279296875:ℝ),(9825593131442763186605487817688/133321100275903651171875:ℝ)],
![(299477874064808206258586690216/8229697547895287109375:ℝ),(71538316246941176717945134501688/666605501379518255859375:ℝ),(70313250565516185753306186230888/666605501379518255859375:ℝ),(7677538210980103465611566212232/222201833793172751953125:ℝ)]]
theorem row046_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (959692276372512933201445776529/13254855684068119412736000000000:ℝ) row046_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row046_coefficients,Fin.sum_univ_succ]
 ring
theorem row046_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row046_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row046_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row046_pos
