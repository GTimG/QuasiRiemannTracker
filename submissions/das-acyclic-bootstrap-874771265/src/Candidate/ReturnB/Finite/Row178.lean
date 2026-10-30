/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row178_coefficients : Fin 3 → Fin 4 → ℝ := ![![(106225244539712555413458825620007577308197/108923255575958048906250000000000:ℝ),(128536569390042561583027053407510641519607/65353953345574829343750000000000:ℝ),(324781054977204043477125561765283617287/319111100320189596405029296875:ℝ),(8361683721926332930162872298360876456/319111100320189596405029296875:ℝ)],
![(53993343698697776919166168785869284297111/27230813893989512226562500000000:ℝ),(328674687348621344842687219663753966189073/81692441681968536679687500000000:ℝ),(675909632633812320102952791324443075044/319111100320189596405029296875:ℝ),(24746243404837942895583265889857787504/319111100320189596405029296875:ℝ)],
![(27519904848050766729620243545206906248573/27230813893989512226562500000000:ℝ),(33749518835549432630314453683803442896831/16338488336393707335937500000000:ℝ),(354024648265557896603989118533555732772/319111100320189596405029296875:ℝ),(17347029785744825213471063218236126616/319111100320189596405029296875:ℝ)]]
theorem row178_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1045210465240791616270359037295109557/311881213648392975946874880000000000000000:ℝ) row178_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row178_coefficients,Fin.sum_univ_succ]
 ring
theorem row178_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row178_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row178_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row178_pos
