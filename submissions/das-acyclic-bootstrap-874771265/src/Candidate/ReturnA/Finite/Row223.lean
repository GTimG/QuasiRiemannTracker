/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row223_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5150577987712815709645653948519527/766395380864310078073710937500:ℝ),(278322072939931449186665330826483821/20692675283336372107990195312500:ℝ),(7782709513823600383507382931916544/1034633764166818605399509765625:ℝ),(4015030794489129321352579816406072/5173168820834093026997548828125:ℝ)],
![(5811159208801497431637284203399694/344877921388939535133169921875:ℝ),(184523078143181438978982362549080018/5173168820834093026997548828125:ℝ),(116315924292550545504266631495799856/5173168820834093026997548828125:ℝ),(18776088921302441440659169185215248/5173168820834093026997548828125:ℝ)],
![(19088668966920806394414356136087028/1724389606944697675665849609375:ℝ),(1816116815069441752576593953310964/72861532687804127140810546875:ℝ),(90838071720624449134537061825758936/5173168820834093026997548828125:ℝ),(19059341827771525761650488923941576/5173168820834093026997548828125:ℝ)]]
theorem row223_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (501878849311141165169072477050759/1205435704327762206639329280000000000:ℝ) row223_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row223_coefficients,Fin.sum_univ_succ]
 ring
theorem row223_pos {δ p : ℝ} (hd : δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row223_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row223_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row223_pos
